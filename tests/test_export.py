"""ink-to-lean tests. Run: python3 -m unittest discover -s tests

Lean checks run when INK_TO_LEAN_LEAN names a Lean 4 binary (or `lean` is on
PATH); otherwise only the translation is tested.
"""
import copy
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from ink_to_lean import export  # noqa: E402
from ink_to_lean.__main__ import failing_theorems, with_sorry  # noqa: E402
from ink_to_lean.export import ident  # noqa: E402

LEAN = os.environ.get('INK_TO_LEAN_LEAN') or shutil.which('lean')


def load(name):
    bundle = json.loads((ROOT / 'examples' / f'{name}.bundle.json').read_text())
    names = json.loads((ROOT / 'examples' / f'{name}.names.json').read_text())['names']
    return bundle, names


def lean_errors(source):
    with tempfile.TemporaryDirectory() as d:
        path = Path(d) / 'Laws.lean'
        path.write_text(source)
        done = subprocess.run([LEAN, str(path)], capture_output=True, text=True, timeout=1800)
        return [l for l in (done.stdout + done.stderr).splitlines() if ': error' in l]


class Export(unittest.TestCase):
    def test_every_law_is_exported_with_a_proof(self):
        for name, count in (('general-laws', 33), ('incremental-laws', 8)):
            bundle, names = load(name)
            source, report = export(bundle, names)
            self.assertEqual(sum(r['status'] == 'exported' for r in report), count)
            self.assertNotIn('sorry', source.split('namespace InkLaws', 1)[1])
            for law in names:
                self.assertIn(f'theorem {ident(law)} ', source)

    def test_general_features_become_binders(self):
        bundle, names = load('general-laws')
        source, _ = export(bundle, names)
        fusion = source[source.index('theorem map_fusion '):].split('\n')[0]
        self.assertIn('{A B C : Type}', fusion)
        self.assertIn('(f : (A → B))', fusion)
        append = source[source.index('theorem fold_append '):].split(':= by')[0]
        self.assertIn('(zero_left : ∀ (a : M), ', append)
        self.assertIn('(associates : ∀ (a : M) (b : M) (c : M), ', append)
        # An instance supplies its assumption proofs.
        instance = source[source.index('theorem sum_append_u64 '):].split('theorem ')[1]
        self.assertIn('@fold_append', instance)

    def test_reserved_names_are_escaped(self):
        self.assertEqual(ident('from'), '«from»')
        self.assertEqual(ident('__assumed_a'), '«__assumed_a»')
        self.assertEqual(ident('xs'), 'xs')

    def test_statements_file_only_replaces_failed_proofs(self):
        src = 'theorem a (x : Nat) :\n    x = x := by\n  rfl\n\ntheorem b :\n    1 = 1 := by\n  rfl\n'
        out = with_sorry(src, {'a'})
        self.assertIn('x = x := by sorry', out)
        self.assertIn('1 = 1 := by\n  rfl', out)
        self.assertEqual(failing_theorems(src, ['L.lean:3:2: error: x']), {'a'})


@unittest.skipUnless(LEAN, 'no Lean binary')
class Lean(unittest.TestCase):
    def test_lean_proves_every_exported_law(self):
        for name in ('general-laws', 'incremental-laws'):
            bundle, names = load(name)
            source, _ = export(bundle, names)
            self.assertEqual(lean_errors(source), [], name)

    def test_a_false_statement_is_not_proved(self):
        bundle, names = load('general-laws')
        bundle = copy.deepcopy(bundle)
        law = bundle['objects'][names['word_wraps']]['payload']
        # x + 4294967295 + 1 == x  becomes  x + 4294967295 + 2 == x
        law['from']['node']['Op'][1][1]['node']['Word'] = 2
        source, _ = export(bundle, {'word_wraps': names['word_wraps']})
        errors = lean_errors(source)
        self.assertEqual(failing_theorems(source, errors), {'word_wraps'})


if __name__ == '__main__':
    unittest.main()

class ContractEvidence(unittest.TestCase):
    def test_contract_envelope_exports_ordinary_laws(self):
        bundle,names=load('general-laws')
        expected=export(bundle,names)
        self.assertEqual(export(dict(semantics='ink-contracts-v1',knowledge=bundle,state_knowledge=None),names),expected)

    def test_structural_float_equality_is_not_ieee_equality(self):
        from ink_to_lean.export import Terms,Unsupported
        def value(t,n):return dict(sort={'Value':t},node=n)
        bits=value('F32',{'Float':0})
        with self.assertRaises(Unsupported):Terms({}).op('value:equal',[bits,bits],{'Value':'Bool'},[])
        floats=value({'List':'F32'},'Nil')
        with self.assertRaises(Unsupported):Terms({}).op('binary:==',[floats,floats],{'Value':'Bool'},[])
        word=value('U32',{'Word':3})
        self.assertIn('decide',Terms({}).op('value:equal',[word,word],{'Value':'Bool'},[]))
