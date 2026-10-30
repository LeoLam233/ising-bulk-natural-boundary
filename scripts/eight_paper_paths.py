"""Verified temporary historical view for unchanged legacy validator cores.

No old public paper/ landing page is recreated. Current Lean is byte-checked
against the pinned base before any view can be constructed.
"""
from pathlib import Path
import atexit,json,shutil,subprocess,tempfile
_views=[]
def historical_root(root,already_verified=False):
 root=Path(root).resolve()
 if (root/'paper').is_dir():return root
 from verify_eight_papers import verify,BASE,PREFIX,RECORD,base_entries
 if not already_verified:verify()
 m=json.loads((root/RECORD).read_text(encoding='utf8'))
 tmp=tempfile.TemporaryDirectory(prefix='eight-paper-historical-');_views.append(tmp)
 target=Path(tmp.name)/'repository'
 # Separate temporary metadata and index; source objects are read-only alternates.
 subprocess.run(['git','init','--quiet',str(target)],check=True)
 objects=subprocess.check_output(['git','-c','safe.directory='+root.as_posix(),'-C',str(root),'rev-parse','--git-path','objects']).decode().strip()
 objects=(root/objects).resolve()
 (target/'.git/objects/info/alternates').write_bytes((objects.as_posix()+'\n').encode('utf8'))
 cmd=['git','-c','safe.directory='+target.as_posix(),'-C',str(target)]
 subprocess.run(cmd+['read-tree',BASE],check=True)
 subprocess.run(cmd+['update-ref','refs/heads/historical-view',BASE],check=True)
 subprocess.run(cmd+['symbolic-ref','HEAD','refs/heads/historical-view'],check=True)
 for rel in base_entries():
  if rel.startswith('paper/'):src=root/PREFIX/rel
  elif rel in m['navigation_and_routing_changes']:src=root/m['historical_navigation_prefix']/rel
  else:src=root/rel
  dst=target/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
 packages=root/'lean/.lake/packages'
 if packages.is_dir():
  (target/'lean/.lake').mkdir(exist_ok=True)
  (target/'lean/.lake/packages').symlink_to(packages.resolve(),target_is_directory=True)
 return target
