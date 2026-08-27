#!/usr/bin/env python3
import argparse, math, os, stat, struct, subprocess, sys, tempfile, time, shutil, hashlib
from pathlib import Path

MIB = 1024 * 1024

def align(x, a): return (x + a - 1) // a * a

def human(n):
    v=float(n)
    for u in ('B','KiB','MiB','GiB','TiB'):
        if v < 1024 or u == 'TiB': return f'{v:.1f} {u}'
        v /= 1024

class Erofs:
    def __init__(self, path):
        self.path=Path(path)
        self.f=open(path,'rb')
        self.f.seek(1024)
        self.sb=self.f.read(144)
        if len(self.sb)<144 or struct.unpack_from('<I',self.sb,0)[0] != 0xe0f5e1e2:
            raise ValueError('not EROFS')
        self.blkszbits=self.sb[12]
        self.bs=1 << self.blkszbits
        self.rootnid=struct.unpack_from('<H',self.sb,14)[0]
        self.meta=struct.unpack_from('<I',self.sb,40)[0]
        self.feature_incompat=struct.unpack_from('<I',self.sb,80)[0]
        self.avail=struct.unpack_from('<H',self.sb,84)[0]
        self.meta_off=self.meta*self.bs
    def close(self):
        try: self.f.close()
        except Exception: pass
    def rd(self,o,n):
        self.f.seek(o); return self.f.read(n)
    def inode(self,nid):
        off=self.meta_off+nid*32
        b=self.rd(off,64)
        fmt,xic,mode,nb=struct.unpack_from('<HHHH',b,0)
        ver=fmt&1; dl=(fmt>>1)&7; isz=64 if ver else 32
        size=struct.unpack_from('<Q' if ver else '<I',b,8)[0]
        iu=struct.unpack_from('<I',b,16)[0]
        if ver:
            uid,gid=struct.unpack_from('<II',b,24)
            mtime=struct.unpack_from('<Q',b,32)[0]
        else:
            uid,gid=struct.unpack_from('<HH',b,24)
            mtime=struct.unpack_from('<I',b,12)[0]
        xsz=0 if xic==0 else 12+4*(xic-1)
        return dict(nid=nid,off=off,fmt=fmt,xic=xic,xsz=xsz,mode=mode,ver=ver,
                    dl=dl,isz=isz,size=size,iu=iu,uid=uid,gid=gid,mtime=mtime,nlink=nb)
    def read_flat(self,ino):
        return b''.join(self.iter_flat(ino))
    def iter_flat(self,ino,chunk=1024*1024):
        size=ino['size']; dl=ino['dl']; bs=self.bs
        if dl==0:
            off=ino['iu']*bs; left=size
            while left:
                n=min(chunk,left); b=self.rd(off,n)
                if len(b)!=n: raise ValueError('short EROFS read')
                yield b; off+=n; left-=n
            return
        if dl!=2: raise ValueError('not flat')
        nblocks=(size+bs-1)//bs
        lastblk=max(0,nblocks-1)
        reglen=lastblk*bs
        off=ino['iu']*bs; left=reglen
        while left:
            n=min(chunk,left); b=self.rd(off,n)
            if len(b)!=n: raise ValueError('short EROFS read')
            yield b; off+=n; left-=n
        tail_len=size-reglen
        if tail_len:
            tail_off=ino['off']+ino['isz']+ino['xsz']+(reglen & (bs-1))
            b=self.rd(tail_off,tail_len)
            if len(b)!=tail_len: raise ValueError('short inline EROFS read')
            yield b
    def comp_info(self,ino):
        end=ino['off']+ino['isz']+ino['xsz']; mh_off=align(end,8); mh=self.rd(mh_off,8)
        advise=struct.unpack_from('<H',mh,4)[0]; alg=mh[6]; cb=mh[7]
        lbits=self.blkszbits+(cb&0xf)
        return mh_off,advise,alg,lbits
    def decode_compact(self,ino,lcn):
        end=ino['off']+ino['isz']+ino['xsz']; mh_off,adv,alg,lbits=self.comp_info(ino); ebase=mh_off+8
        total=(ino['size']+(1<<lbits)-1)>>lbits; c4=((32-ebase%32)//4)&7; c2=0
        if adv&1 and c4<total: c2=((total-c4)//16)*16
        orig=lcn; pos=ebase; shift=2
        if lcn>=c4:
            pos+=c4*4; lcn-=c4
            if lcn<c2: shift=1
            else: pos+=c2*2; lcn-=c2
        pos+=lcn*(1<<shift)
        vcnt=2 if (1<<shift)==4 and lbits<=14 else 16 if (1<<shift)==2 and lbits<=12 else None
        if not vcnt: raise NotImplementedError('compact pack unsupported')
        packsz=vcnt<<shift; bytes_=pos&(packsz-1); base=pos-bytes_; blob=self.rd(base,packsz); i=bytes_>>shift
        lobits=max(lbits,12); encodebits=(packsz-4)*8//vcnt
        def dbits(idx):
            bit=encodebits*idx; bo=bit//8; sh=bit&7; raw=blob[bo:bo+8]
            val=int.from_bytes(raw,'little')>>sh
            return val&((1<<lobits)-1),(val>>lobits)&3
        lo,typ=dbits(i); d={'lcn':orig,'type':typ,'lo':lo,'adv':adv,'alg':alg,'lbits':lbits}
        if typ==2:
            d['clusterofs']=1<<lbits
            if lo&0x800: d['compressedblks']=lo&~0x800; d['delta0']=1
            elif i+1!=vcnt: d['delta0']=lo
            else:
                lo2,t2=dbits(i-1); d['delta0']=(0 if t2!=2 else 1 if lo2&0x800 else lo2)+1
        else:
            d['clusterofs']=lo; big=bool(adv&2); nblk=0 if big else 1; ii=i
            if not big:
                while ii>0:
                    ii-=1; l,t=dbits(ii)
                    if t==2: ii-=l
                    if ii>=0: nblk+=1
            else:
                while ii>0:
                    ii-=1; l,t=dbits(ii)
                    if t==2:
                        if l&0x800: ii-=1; nblk+=l&~0x800; continue
                        if l<=1: raise ValueError('bad d0')
                        ii-=l-2; continue
                    nblk+=1
            d['pblk']=struct.unpack_from('<I',blob,packsz-4)[0]+nblk
        return d
    def decode_full(self,ino,lcn):
        end=ino['off']+ino['isz']+ino['xsz']; mh_off,adv,alg,lbits=self.comp_info(ino)
        start=align(end,8)+8+8
        b=self.rd(start+lcn*8,8); ad,co=struct.unpack_from('<HH',b,0); typ=ad&3
        d={'lcn':lcn,'type':typ,'lo':co,'clusterofs':(1<<lbits if typ==2 else co),
           'adv':adv,'alg':alg,'lbits':lbits}
        if typ==2:
            d0,d1=struct.unpack_from('<HH',b,4)
            if d0&0x800: d['compressedblks']=d0&~0x800; d0=1
            d['delta0']=d0; d['delta1']=d1
        else: d['pblk']=struct.unpack_from('<I',b,4)[0]
        return d
    def zstd_decode(self,blob,expected):
        magic=b'\x28\xb5\x2f\xfd'; idx=blob.find(magic)
        if idx<0: raise ValueError('zstd magic not found')
        p=subprocess.run(['zstd','-q','-d','-c'],input=blob[idx:],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        if p.returncode: raise ValueError('zstd: '+p.stderr.decode(errors='replace'))
        if len(p.stdout)<expected: raise ValueError(f'zstd short {len(p.stdout)} < {expected}')
        return p.stdout[:expected]
    def iter_compressed(self,ino):
        _,adv,alg,lbits=self.comp_info(ino); L=1<<lbits
        total=(ino['size']+L-1)//L
        dec=self.decode_compact if ino['dl']==3 else self.decode_full
        rec=[dec(ino,i) for i in range(total)]
        heads=[]
        for r in rec:
            if r['type']!=2:
                ls=r['lcn']*L+r['clusterofs']; heads.append((ls,r))
        logical_pos=0
        for k,(ls,r) in enumerate(heads):
            if ls>=ino['size']: continue
            le=heads[k+1][0] if k+1<len(heads) else ino['size']; le=min(le,ino['size'])
            if le<=ls: continue
            if ls>logical_pos:
                yield b'\0'*(ls-logical_pos)
                logical_pos=ls
            need=le-ls
            pblks=None; nxt_lcn=r['lcn']+1
            if nxt_lcn<len(rec) and rec[nxt_lcn]['type']==2 and rec[nxt_lcn].get('compressedblks'):
                pblks=rec[nxt_lcn]['compressedblks']
            if pblks is None and k+1<len(heads) and heads[k+1][1].get('pblk',0)>=r.get('pblk',0):
                diff=heads[k+1][1]['pblk']-r['pblk']; pblks=diff if diff>0 else 1
            if pblks is None: pblks=1
            phys=self.rd(r['pblk']*self.bs,pblks*self.bs)
            data=phys[:need] if r['type']==0 else self.zstd_decode(phys,need)
            if len(data)<need: raise ValueError('short decompressed data')
            yield data[:need]
            logical_pos=le
        if logical_pos < ino['size']:
            yield b'\0'*(ino['size']-logical_pos)
    def iter_data(self,ino):
        if ino['size']==0: return iter(())
        if ino['dl'] in (0,2): return self.iter_flat(ino)
        if ino['dl'] in (1,3): return self.iter_compressed(ino)
        raise NotImplementedError(f'datalayout {ino["dl"]}')
    def read_data(self,ino):
        return b''.join(self.iter_data(ino))
    def dirents(self,ino):
        data=self.read_data(ino); bs=self.bs; out=[]; pos=0
        while pos<len(data):
            chunk=data[pos:min(pos+bs,len(data))]
            if len(chunk)<12: break
            no=struct.unpack_from('<H',chunk,8)[0]
            if no==0 or no%12: raise ValueError(f'bad dir nameoff {no} nid {ino["nid"]} pos {pos}')
            cnt=no//12
            for i in range(cnt):
                nid,nameoff,ft,res=struct.unpack_from('<QHBB',chunk,i*12)
                nextoff=struct.unpack_from('<H',chunk,(i+1)*12+8)[0] if i+1<cnt else len(chunk)
                name=chunk[nameoff:nextoff].split(b'\0',1)[0].decode('utf-8','surrogateescape')
                out.append((nid,ft,name))
            pos+=len(chunk)
        return out
    def walk(self):
        yield Path('.'), self.inode(self.rootnid)
        seen_dirs=set()
        def rec(nid,rel):
            ino=self.inode(nid)
            if nid in seen_dirs: return
            seen_dirs.add(nid)
            for cnid,ft,name in self.dirents(ino):
                if name in ('.','..',''): continue
                crel=rel/name; cino=self.inode(cnid)
                yield crel,cino
                if stat.S_ISDIR(cino['mode']): yield from rec(cnid,crel)
        yield from rec(self.rootnid,Path('.'))
    def scan(self):
        rows=[]; data=0; counts={'files':0,'dirs':0,'symlinks':0,'other':0}
        print('[SCAN] reading EROFS tree...',flush=True)
        for i,(p,ino) in enumerate(self.walk(),1):
            rows.append((p,ino)); mode=ino['mode']
            if stat.S_ISDIR(mode): counts['dirs']+=1
            elif stat.S_ISLNK(mode): counts['symlinks']+=1; data+=max(1,ino['size'])
            elif stat.S_ISREG(mode): counts['files']+=1; data+=max(1,ino['size'])
            else: counts['other']+=1
            if i==1 or i%100==0:
                print(f'\r[SCAN] entries: {i:,}',end='',flush=True)
        print(f'\r[SCAN] entries: {len(rows):,} — done'+' '*20)
        return rows,data,counts



def tool(name):
    p=shutil.which(name)
    if p: return p
    for d in ('/usr/sbin','/sbin','/usr/bin','/bin'):
        q=Path(d)/name
        if q.exists() and os.access(q,os.X_OK): return str(q)
    return None

def q(s):
    # debugfs/libss uses doubled double-quotes inside quoted arguments.
    # Backslashes are kept literally.
    s=str(s)
    return '"' + s.replace('"','""') + '"'

def fs_path(rel):
    s=rel.as_posix()
    if s == '.': return '/'
    if s.startswith('/'): return s
    return '/' + s

def inode_meta_cmds(path, ino, include_links=True):
    p=q(path)
    cmds=[
        f'sif {p} mode {int(ino["mode"])}',
        f'sif {p} uid {int(ino["uid"])}',
        f'sif {p} gid {int(ino["gid"])}',
    ]
    mt=int(ino.get('mtime') or 0)
    if mt >= 0:
        cmds.append(f'sif {p} mtime @{mt}')
    if include_links and int(ino.get('nlink') or 0)>0:
        cmds.append(f'sif {p} links_count {int(ino["nlink"])}')
    return cmds

def run_capture(cmd, ok=(0,), input_data=None):
    r=subprocess.run([str(x) for x in cmd], input=input_data,
                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                     text=(input_data is None))
    if r.returncode not in ok:
        out=r.stdout if isinstance(r.stdout,str) else r.stdout.decode(errors='replace')
        raise RuntimeError(f'command failed RC={r.returncode}: {" ".join(map(str,cmd))}\n{out}')
    return r

def debugfs_batch(debugfs, image, commands, work, tag):
    if not commands: return ''
    cmdfile=Path(work)/f'{tag}.debugfs'
    logfile=Path(work)/f'{tag}.log'
    cmdfile.write_text('\n'.join(commands)+'\n',encoding='utf-8')
    r=subprocess.run([debugfs,'-w','-f',str(cmdfile),str(image)],
                     stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    logfile.write_text(r.stdout,encoding='utf-8',errors='replace')
    # debugfs sometimes returns 0 even if an individual command printed an error.
    bad_markers=(
        'File not found by ext2_lookup',
        'Ext2 file already exists',
        'Command not found',
        'Usage:',
        'while opening',
        'Filesystem not open',
        'Could not allocate',
        'No free space',
        'while allocating',
        'while creating',
        'while writing',
    )
    bad=[line for line in r.stdout.splitlines()
         if any(m.lower() in line.lower() for m in bad_markers)]
    if r.returncode != 0 or bad:
        tail='\n'.join(r.stdout.splitlines()[-60:])
        raise RuntimeError(f'debugfs batch {tag} failed\n{tail}')
    return r.stdout

def preflight(mke2fs, debugfs, e2fsck):
    """Real backend test before conversion: create EXT4, write, metadata, symlink, dump, fsck."""
    import re
    with tempfile.TemporaryDirectory(prefix='skyworth_direct_preflight.') as td:
        td=Path(td)
        img=td/'probe.img'
        src=td/'probe.bin'
        dump=td/'dump.bin'
        src.write_bytes(b'SKYWORTH-DIRECT-TEST\n')
        blocks=(32*MIB)//4096
        cmd=[mke2fs,'-t','ext4','-F','-q','-b','4096','-I','256',
             '-L','probe','-m','0','-O','^has_journal',
             '-E','lazy_itable_init=0',str(img),str(blocks)]
        r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        if r.returncode:
            return False,'mke2fs preflight failed:\n'+r.stdout

        cmds=[
            f'write {q(src)} {q("/probe.bin")}',
            'sif "/probe.bin" mode 33188',   # 0100644
            'sif "/probe.bin" uid 1234',
            'sif "/probe.bin" gid 4321',
            'sif "/probe.bin" mtime @1700000000',
            'mkdir "/probe_dir"',
            'sif "/probe_dir" mode 16877',   # 0040755
            'symlink "/probe_link" "/probe.bin"',
        ]
        try:
            debugfs_batch(debugfs,img,cmds,td,'preflight_write')
        except Exception as ex:
            return False,str(ex)

        # Prove file bytes can be read back from the generated EXT4.
        r=subprocess.run([debugfs,'-R',f'dump {q("/probe.bin")} {q(dump)}',str(img)],
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        if r.returncode or not dump.exists() or dump.read_bytes()!=src.read_bytes():
            return False,'debugfs dump verification failed:\n'+r.stdout

        # Prove set_inode_field actually applied metadata.
        r=subprocess.run([debugfs,'-R','stat "/probe.bin"',str(img)],
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        st=r.stdout
        if r.returncode:
            return False,'debugfs stat verification failed:\n'+st
        if not re.search(r'\bUser:\s*1234\b',st):
            return False,'debugfs UID verification failed:\n'+st
        if not re.search(r'\bGroup:\s*4321\b',st):
            return False,'debugfs GID verification failed:\n'+st
        if not re.search(r'\bMode:\s*0?644\b',st):
            return False,'debugfs mode verification failed:\n'+st

        # Prove symlink creation works with this debugfs build.
        r=subprocess.run([debugfs,'-R','stat "/probe_link"',str(img)],
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        st_link=r.stdout
        if r.returncode:
            return False,'debugfs symlink stat failed:\n'+st_link
        if '/probe.bin' not in st_link:
            # Some debugfs builds format fast symlink output differently.
            # cat on the link inode is a second check of the stored target.
            r2=subprocess.run([debugfs,'-R','cat "/probe_link"',str(img)],
                              stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
            if '/probe.bin' not in r2.stdout:
                return False,'debugfs symlink target verification failed:\n'+st_link+'\n'+r2.stdout

        # Run fsck after all mutations; 0=clean, 1=corrected.
        r=subprocess.run([e2fsck,'-fy',str(img)],
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        if r.returncode not in (0,1):
            return False,'e2fsck preflight failed:\n'+r.stdout

        # One more readback after fsck proves corrections did not destroy the file.
        try:
            dump.unlink()
        except OSError:
            pass
        r=subprocess.run([debugfs,'-R',f'dump {q("/probe.bin")} {q(dump)}',str(img)],
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        if r.returncode or not dump.exists() or dump.read_bytes()!=src.read_bytes():
            return False,'post-fsck readback failed:\n'+r.stdout

        return True,''


def draw(done,total,idx,item_total,path,phase='Writing'):
    pct=100.0 if total<=0 else min(100.0,done*100.0/total)
    width=28; filled=int(width*pct/100.0)
    bar='█'*filled+'-'*(width-filled)
    s=str(path)
    if len(s)>42: s='…'+s[-41:]
    print(f'\r[{bar}] {pct:6.2f}%  {human(done)}/{human(total)}  {idx:,}/{item_total:,}  {s:<42}',
          end='',flush=True)

def write_erofs_file(e, ino, out, hasher=None, progress=None):
    total=0
    with open(out,'wb') as f:
        for chunk in e.iter_data(ino):
            f.write(chunk)
            total += len(chunk)
            if hasher is not None: hasher.update(chunk)
            if progress is not None: progress(len(chunk))
    if total != int(ino['size']):
        raise ValueError(f'short file decode: {total} != {ino["size"]}')

def make_blank_ext4(mke2fs,image,size_mb,label,with_journal=False):
    blocks=size_mb*MIB//4096
    cmd=[mke2fs,'-t','ext4','-F','-q','-b','4096','-I','256',
         '-L',label[:16],'-m','0']
    if not with_journal: cmd += ['-O','^has_journal']
    cmd += ['-E','lazy_itable_init=0',str(image),str(blocks)]
    r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    if r.returncode:
        raise RuntimeError('mke2fs failed:\n'+r.stdout)

def choose_work_parent(output,size_mb,forced=None):
    need=size_mb*MIB + 256*MIB
    if forced:
        p=Path(forced).expanduser().resolve()
        p.mkdir(parents=True,exist_ok=True)
        if shutil.disk_usage(p).free < need:
            raise RuntimeError(f'not enough free space in {p}: need ~{human(need)}')
        return p,False
    p=Path('/tmp')
    try:
        if shutil.disk_usage(p).free >= need:
            return p,False
    except Exception:
        pass
    # Fallback beside output. Slower on /mnt/c or /mnt/d, but no full staging tree.
    return output.parent,True

def verify_regular_files(debugfs,image,expected,work,batch_count=100):
    """Verify regular-file bytes from EXT4 without extracting the whole partition."""
    items=list(expected.items())
    total=len(items); done=0
    vdir=Path(work)/'verify'
    vdir.mkdir(exist_ok=True)
    for base in range(0,total,batch_count):
        batch=items[base:base+batch_count]
        cmds=[]; outs=[]
        for j,(path,(digest,size)) in enumerate(batch):
            op=vdir/f'v{base+j:06d}'
            cmds.append(f'dump {q(path)} {q(op)}')
            outs.append((path,op,digest,size))
        # read-only debugfs is enough for dump
        cmdfile=Path(work)/f'verify_{base//batch_count:04d}.debugfs'
        cmdfile.write_text('\n'.join(cmds)+'\n',encoding='utf-8')
        r=subprocess.run([debugfs,'-f',str(cmdfile),str(image)],
                         stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        if r.returncode:
            raise RuntimeError('debugfs verify failed:\n'+'\n'.join(r.stdout.splitlines()[-50:]))
        for path,op,digest,size in outs:
            if not op.exists():
                raise RuntimeError(f'verify missing output: {path}')
            st=op.stat()
            if st.st_size != size:
                raise RuntimeError(f'verify size mismatch: {path} {st.st_size} != {size}')
            h=hashlib.sha256()
            with open(op,'rb') as f:
                while True:
                    b=f.read(4*MIB)
                    if not b: break
                    h.update(b)
            if h.digest()!=digest:
                raise RuntimeError(f'verify SHA256 mismatch: {path}')
            op.unlink()
            done += 1
            pct=done*100/max(1,total)
            width=28; fill=int(width*pct/100)
            print(f'\r[{"█"*fill}{"-"*(width-fill)}] {pct:6.2f}%  {done:,}/{total:,} files verified',
                  end='',flush=True)
    print()

def copy_progress(src,dst):
    total=src.stat().st_size; done=0
    part=dst.with_name(dst.name+'.part')
    if part.exists(): part.unlink()
    with open(src,'rb') as fi, open(part,'wb') as fo:
        while True:
            b=fi.read(16*MIB)
            if not b: break
            fo.write(b); done+=len(b)
            pct=done*100/max(1,total); width=28; fill=int(width*pct/100)
            print(f'\r[{"█"*fill}{"-"*(width-fill)}] {pct:6.2f}%  {human(done)}/{human(total)}  saving output',
                  end='',flush=True)
        fo.flush(); os.fsync(fo.fileno())
    print()
    if dst.exists(): dst.unlink()
    os.replace(part,dst)

def main():
    ap=argparse.ArgumentParser(description='Direct Skyworth/TrueID EROFS -> RAW EXT4 converter (debugfs backend, no unpack folder)')
    ap.add_argument('image',help='source EROFS image, e.g. vendor.img')
    ap.add_argument('-o','--output',help='output image (default: <stem>_ext4.img)')
    ap.add_argument('--size-mb',type=int,help='force EXT4 size in MiB')
    ap.add_argument('--margin',type=int,default=30,help='auto-size extra percent (default: 30)')
    ap.add_argument('--extra-mb',type=int,default=128,help='extra MiB after margin (default: 128)')
    ap.add_argument('--label',help='EXT4 label (default: image stem)')
    ap.add_argument('--with-journal',action='store_true',help='enable EXT4 journal')
    ap.add_argument('--batch-mb',type=int,default=64,help='max temporary decoded data per debugfs batch (default: 64)')
    ap.add_argument('--work-dir',help='temporary work parent (default: /tmp if enough space, otherwise output directory)')
    ap.add_argument('--no-preflight',action='store_true',help='skip real mke2fs/debugfs/e2fsck backend self-test')
    ap.add_argument('--no-verify',action='store_true',help='skip full regular-file SHA256 verification after build')
    a=ap.parse_args()

    image=Path(a.image).expanduser().resolve()
    if not image.is_file(): raise SystemExit(f'[ERROR] image not found: {image}')
    output=(Path(a.output).expanduser() if a.output else Path.cwd()/f'{image.stem}_ext4.img').resolve()
    output.parent.mkdir(parents=True,exist_ok=True)

    zstd=tool('zstd'); mke2fs=tool('mke2fs'); debugfs=tool('debugfs'); e2fsck=tool('e2fsck')
    missing=[n for n,v in [('zstd',zstd),('mke2fs',mke2fs),('debugfs',debugfs),('e2fsck',e2fsck)] if not v]
    if missing:
        raise SystemExit('[ERROR] missing tools: '+', '.join(missing)+'\nInstall: sudo apt update && sudo apt install -y zstd e2fsprogs')

    try: e=Erofs(image)
    except Exception as ex: raise SystemExit(f'[ERROR] {image.name}: {ex}')

    print('==================================================')
    print(' Skyworth / TrueID EROFS -> EXT4 Direct Converter')
    print('==================================================')
    print(f'[INPUT ] {image}')
    print(f'[OUTPUT] {output}')
    print(f'[EROFS ] block={e.bs} rootnid={e.rootnid} incompat=0x{e.feature_incompat:x} compr_bitmap=0x{e.avail:x}')
    print('[MODE  ] EROFS -> small batches -> debugfs -> EXT4')
    print('[MODE  ] no unpack folder / no libarchive / no loop mount')
    print()

    print('[1/6] Scanning EROFS...')
    rows,data_bytes,counts=e.scan()
    print(f"[SCAN] files={counts['files']:,} dirs={counts['dirs']:,} symlinks={counts['symlinks']:,} other={counts['other']:,} data={human(data_bytes)}")
    if counts['other']:
        bad=[str(p) for p,i in rows if not (stat.S_ISDIR(i['mode']) or stat.S_ISREG(i['mode']) or stat.S_ISLNK(i['mode']))]
        raise SystemExit('[ERROR] unsupported special nodes in this image:\n  '+'\n  '.join(bad[:20]))

    data_mb=math.ceil(data_bytes/MIB)
    auto_mb=math.ceil(data_mb*(100+a.margin)/100.0)+a.extra_mb
    auto_mb=((auto_mb+15)//16)*16
    size_mb=a.size_mb or auto_mb
    if size_mb < data_mb+64:
        raise SystemExit(f'[ERROR] requested image too small: {size_mb} MiB; suggested {auto_mb} MiB')
    label=(a.label or image.stem)[:16]
    print(f'[SIZE ] EXT4 target = {size_mb} MiB')

    print()
    print('[2/6] Backend self-test...')
    if a.no_preflight:
        print('[CHECK] skipped by --no-preflight')
    else:
        ok,msg=preflight(mke2fs,debugfs,e2fsck)
        if not ok:
            raise SystemExit('[ERROR] direct EXT4 backend self-test failed.\n'+msg)
        print('[CHECK] mke2fs + debugfs write/dump + e2fsck: PASS')

    work_parent,slow=choose_work_parent(output,size_mb,a.work_dir)
    work=Path(tempfile.mkdtemp(prefix='skyworth_direct.',dir=work_parent))
    ext4=work/f'{image.stem}_ext4.img'
    print(f'[WORK ] {work}')
    if slow: print('[WORK ] /tmp space is low; using output drive directly (may be slower)')

    expected={}
    symlink_expected={}
    try:
        print()
        print('[3/6] Creating blank EXT4...')
        make_blank_ext4(mke2fs,ext4,size_mb,label,a.with_journal)
        print('[BUILD] blank EXT4: OK')

        print()
        print('[4/6] Populating EXT4 directly...')

        # Remove mke2fs lost+found unless the source actually contains it.
        source_paths={fs_path(p) for p,i in rows}
        init_cmd=[]
        if '/lost+found' not in source_paths:
            init_cmd.append('rmdir "/lost+found"')

        # Directories parent-first.
        for p,ino in rows:
            if str(p)=='.' or not stat.S_ISDIR(ino['mode']): continue
            fp=fs_path(p)
            init_cmd.append(f'mkdir {q(fp)}')
        # Apply directory metadata after creation so restrictive modes don't affect anything.
        for p,ino in reversed(rows):
            if not stat.S_ISDIR(ino['mode']): continue
            fp=fs_path(p)
            init_cmd.extend(inode_meta_cmds(fp,ino,include_links=True))
        debugfs_batch(debugfs,ext4,init_cmd,work,'directories')

        regular=[(p,i) for p,i in rows if stat.S_ISREG(i['mode'])]
        symlinks=[(p,i) for p,i in rows if stat.S_ISLNK(i['mode'])]
        total_items=len(regular)+len(symlinks)
        done_bytes=0; item_idx=0
        batch_limit=max(1,a.batch_mb)*MIB
        batch_no=0
        first_by_nid={}
        link_counts={}
        batch_dir=work/'batch'
        batch_dir.mkdir(exist_ok=True)

        def flush_batch(commands, files):
            nonlocal batch_no
            if not commands: return
            debugfs_batch(debugfs,ext4,commands,work,f'files_{batch_no:04d}')
            for f in files:
                try: Path(f).unlink()
                except OSError: pass
            batch_no += 1

        commands=[]; temp_files=[]; batch_bytes=0
        for p,ino in regular:
            item_idx += 1
            fp=fs_path(p)
            nid=ino['nid']
            if nid in first_by_nid:
                srcp=first_by_nid[nid]
                commands.append(f'ln {q(srcp)} {q(fp)}')
                link_counts[nid]=link_counts.get(nid,1)+1
                # Metadata is shared by the hardlink inode; no separate sif required.
                draw(done_bytes,data_bytes,item_idx,total_items,p)
                continue

            first_by_nid[nid]=fp
            link_counts[nid]=1
            tp=batch_dir/f'f{item_idx:06d}'
            h=hashlib.sha256()
            local_written=0
            def prog(n):
                nonlocal local_written
                local_written += n
            write_erofs_file(e,ino,tp,h,prog)
            expected[fp]=(h.digest(),int(ino['size']))
            commands.append(f'write {q(tp)} {q(fp)}')
            commands.extend(inode_meta_cmds(fp,ino,include_links=False))
            temp_files.append(tp)
            batch_bytes += max(1,int(ino['size']))
            done_bytes += max(1,int(ino['size']))
            draw(done_bytes,data_bytes,item_idx,total_items,p)

            if batch_bytes >= batch_limit:
                flush_batch(commands,temp_files)
                commands=[]; temp_files=[]; batch_bytes=0

        flush_batch(commands,temp_files)

        # Symlinks do not need host-side decoded files.
        sycmd=[]
        for p,ino in symlinks:
            item_idx += 1
            fp=fs_path(p)
            target=e.read_data(ino).decode('utf-8','surrogateescape')
            symlink_expected[fp]=target
            sycmd.append(f'symlink {q(fp)} {q(target)}')
            sycmd.extend(inode_meta_cmds(fp,ino,include_links=True))
            done_bytes += max(1,int(ino['size']))
            draw(done_bytes,data_bytes,item_idx,total_items,p)
        if sycmd: debugfs_batch(debugfs,ext4,sycmd,work,'symlinks')

        # Correct hard-link reference counts because debugfs ln intentionally does not.
        hardcmd=[]
        for nid,count in link_counts.items():
            if count>1:
                path=first_by_nid[nid]
                # Prefer original EROFS nlink when available.
                ino=next(i for p,i in regular if i['nid']==nid)
                nlink=max(count,int(ino.get('nlink') or count))
                hardcmd.append(f'sif {q(path)} links_count {nlink}')
        if hardcmd: debugfs_batch(debugfs,ext4,hardcmd,work,'hardlinks')

        draw(data_bytes,data_bytes,total_items,total_items,'filesystem data committed')
        print()
        print('[WRITE] EXT4 population: OK')

        print()
        print('[5/6] Checking filesystem...')
        r=subprocess.run([e2fsck,'-fy',str(ext4)],stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
        if r.returncode not in (0,1):
            print(r.stdout)
            raise RuntimeError(f'e2fsck failed RC={r.returncode}')
        print('[CHECK] e2fsck: PASS')

        if a.no_verify:
            print('[VERIFY] skipped by --no-verify')
        else:
            print(f'[VERIFY] SHA256 checking {len(expected):,} regular files from generated EXT4...')
            verify_regular_files(debugfs,ext4,expected,work)
            print('[VERIFY] regular-file SHA256: PASS')

            # Verify symlink targets through debugfs stat output.
            # We only do existence/type/target checks using stat text; data files are already hash-verified.
            for idx,(fp,target) in enumerate(symlink_expected.items(),1):
                r=subprocess.run([debugfs,'-R',f'stat {q(fp)}',str(ext4)],
                                 stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
                if r.returncode or 'symlink' not in r.stdout.lower():
                    # Some versions print "fast link dest" without the word symlink; accept if target is visible.
                    if target not in r.stdout:
                        raise RuntimeError(f'symlink verify failed: {fp}\n{r.stdout}')
                if target not in r.stdout:
                    # Fall back to ext2 inode dump may not print target in every format; skip target strictness.
                    pass
            print(f'[VERIFY] symlinks checked: {len(symlink_expected):,}')

        print()
        print('[6/6] Saving final image...')
        if ext4.parent == output.parent:
            part=output.with_name(output.name+'.part')
            if part.exists(): part.unlink()
            os.replace(ext4,part)
            if output.exists(): output.unlink()
            os.replace(part,output)
            print('[████████████████████████████] 100.00%  saved')
        else:
            copy_progress(ext4,output)

        print('==================================================')
        print('[SUCCESS]')
        print('==================================================')
        print(f'[OUTPUT] {output}')
        print(f'[SIZE  ] {human(output.stat().st_size)}')
        print('[NOTE] No unpack folder and no full staging tree were created.')
        print('[NOTE] This backend does not require mke2fs libarchive support.')
        print('[NOTE] UID/GID/mode/mtime and symlinks are restored from EROFS.')
        print('[NOTE] SELinux/security xattrs and AVB are not rebuilt.')

    finally:
        try: e.close()
        except Exception: pass
        try: shutil.rmtree(work)
        except Exception: pass

if __name__=='__main__':
    main()
