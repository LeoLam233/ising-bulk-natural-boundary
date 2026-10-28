#!/usr/bin/env python3
"""Bounded filesystem tests; no Lean, build, or dependency graph is executed."""
import contextlib,hashlib,io,json,os,pathlib,tempfile,unittest
from unittest.mock import patch
from run_controls import read_manifest,check_manifest,prepare_portable_overlay,mandatory_inputs
import make_graph_driver

class RunnerControls(unittest.TestCase):
    def test_manifest_string_and_object_digest(self):
        with tempfile.TemporaryDirectory() as d:
            root=pathlib.Path(d);source=root/'source';source.write_text('frozen')
            digest=hashlib.sha256(source.read_bytes()).hexdigest()
            manifest=root/'manifest.json'
            for value in (digest,dict(sha256=digest,size=6)):
                manifest.write_text(json.dumps(dict(files={'source':value})))
                pinned,files=read_manifest(manifest)
                check_manifest(manifest,pinned,files,campaign=root)

    def test_manifest_cannot_be_rewritten_alongside_source(self):
        with tempfile.TemporaryDirectory() as d:
            root=pathlib.Path(d);source=root/'source';source.write_text('frozen')
            manifest=root/'manifest.json'
            manifest.write_text(json.dumps(dict(files={'source':hashlib.sha256(source.read_bytes()).hexdigest()})))
            pinned,files=read_manifest(manifest)
            source.write_text('replacement')
            manifest.write_text(json.dumps(dict(files={'source':hashlib.sha256(source.read_bytes()).hexdigest()})))
            with self.assertRaisesRegex(ValueError,'manifest changed'):
                check_manifest(manifest,pinned,files,campaign=root)

    def test_source_change_and_escape_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            root=pathlib.Path(d);source=root/'source';source.write_text('frozen')
            digest=hashlib.sha256(source.read_bytes()).hexdigest();manifest=root/'manifest.json'
            manifest.write_text(json.dumps(dict(files={'source':digest})))
            pinned,files=read_manifest(manifest);source.write_text('changed')
            with self.assertRaisesRegex(ValueError,'source mismatch'):
                check_manifest(manifest,pinned,files,campaign=root)
            with self.assertRaisesRegex(ValueError,'not campaign-relative'):
                check_manifest(manifest,pinned,{str(source):digest},campaign=root)
            with self.assertRaises(ValueError):
                check_manifest(manifest,pinned,{'../escape':digest},campaign=root)

    def test_mandatory_nested_aggregate_and_scanner(self):
        required=mandatory_inputs()
        for name in ('repository/lean/IsingBulk/HT22.lean','repository/lean/lakefile.ht22.toml',
                     'repository/verification/lt22/RootWalker.lean','verification_controls/make_graph_driver.py'):
            self.assertIn(name,required)
        self.assertFalse(any('/generated/' in name or '/runs/' in name for name in required))

    def test_portable_overlay_merges_namespace_without_mutating_inputs(self):
        with tempfile.TemporaryDirectory() as d:
            root=pathlib.Path(d);project=root/'project';upstream=root/'upstream';overlay=root/'overlay'
            files={project/'IsingBulk/HT22/PhysicalScope/RealSpin.olean':'physical',
                   project/'IsingBulk/HT/Final/Inversion.olean':'protected',
                   project/'IsingBulk/HT22/Controls/Basic.olean':'old control',
                   upstream/'Mathlib/Basic.olean':'mathlib',
                   upstream/'IsingBulk/Other/Helper.olean':'merged namespace'}
            for path,content in files.items():path.parent.mkdir(parents=True,exist_ok=True);path.write_text(content)
            prepare_portable_overlay(overlay,os.pathsep.join(map(str,(project,upstream))))
            for path,content in files.items():
                relative=path.relative_to(project if path.is_relative_to(project) else upstream)
                if relative.as_posix()=='IsingBulk/HT22/Controls/Basic.olean':
                    self.assertFalse((overlay/relative).exists());continue
                self.assertEqual((overlay/relative).read_text(),content)
            target=overlay/'IsingBulk/HT22/Controls/Basic.olean';target.write_text('fresh control')
            self.assertFalse(target.is_symlink())
            for path,content in files.items():self.assertEqual(path.read_text(),content)

    def test_snapshot_graph_driver_uses_pinned_baseline_without_git(self):
        with tempfile.TemporaryDirectory() as d:
            root=pathlib.Path(d);here=root/'verification_controls';here.mkdir()
            scanner=root/'repository/verification/lt22/RootWalker.lean'
            scanner.parent.mkdir(parents=True);data=b'import Lean\n-- exact protected scanner body\n'
            scanner.write_bytes(data)
            baseline=root/'PROTECTED_BASELINE.json'
            baseline.write_text(json.dumps(dict(commit=make_graph_driver.COMMIT,files={
                'verification/lt22/RootWalker.lean':dict(sha256=hashlib.sha256(data).hexdigest(),
                    git_blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest(),mode='100644')})))
            output=here/'generated/FinalGraph.lean';graph=here/'generated/final'
            argv=['make_graph_driver.py','--case','final','--module','IsingBulkHT22',
                  '--output',str(output),'--graph-base',str(graph)]
            with patch.object(make_graph_driver,'ROOT',root),patch.object(make_graph_driver,'HERE',here),\
                    patch('sys.argv',argv),patch.object(make_graph_driver.subprocess,'check_output') as git,\
                    contextlib.redirect_stdout(io.StringIO()):
                make_graph_driver.main()
                git.assert_not_called()
                self.assertIn('-- exact protected scanner body',output.read_text())
                receipt=json.loads(output.with_suffix('.driver.json').read_text())
                self.assertFalse(receipt['executed'])
                scanner.write_bytes(data+b'-- mutated\n')
                with self.assertRaisesRegex(SystemExit,'identity mismatch'):make_graph_driver.main()

if __name__=='__main__':unittest.main(verbosity=2)
