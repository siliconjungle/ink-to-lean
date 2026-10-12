"""ink-to-lean: export an Ink law bundle to a Lean 4 file and optionally check it.

  python3 -m ink_to_lean BUNDLE.json [--names RECEIPT.json] -o Laws.lean
      [--lean PATH] [--check] [--statements Statements.lean] [--report REPORT.json]

BUNDLE.json is written by `ink emit-laws SOURCE -o BUNDLE.json`; its stdout
receipt (`--names`) supplies law names. With `--check`, Lean checks the file;
theorems whose exported proofs fail are reported, and `--statements` writes a
copy where only those proofs are `sorry` (statements are never changed).
"""
import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

from .export import export,ident


def check(lean, path):
    done = subprocess.run([lean, str(path)], capture_output=True, text=True, timeout=1800)
    errors = [line for line in (done.stdout + done.stderr).splitlines() if ': error' in line]
    return done.returncode, errors, done.stdout + done.stderr


def failing_theorems(source, errors):
    """Theorems containing an error line."""
    starts = [(i + 1, m.group(1)) for i, line in enumerate(source.splitlines())
              if (m := re.match(r'theorem (\S+)', line))]
    bad = set()
    for e in errors:
        m = re.search(r':(\d+):\d+: error', e)
        if not m:
            continue
        line = int(m.group(1))
        owner = None
        for start, name in starts:
            if start <= line:
                owner = name
        if owner:
            bad.add(owner)
    return bad


def with_sorry(source, names):
    """Replace only the proofs of the named theorems with `sorry`."""
    out, state = [], 'copy'
    for line in source.splitlines():
        m = re.match(r'theorem (\S+)', line)
        if m:
            state = 'statement' if m.group(1) in names else 'copy'
        if state == 'proof':
            if line.startswith(' '):
                continue
            state = 'copy'
        if state == 'statement' and line.rstrip().endswith(':= by'):
            out.append(line.rstrip() + ' sorry')
            state = 'proof'
            continue
        out.append(line)
    return '\n'.join(out) + '\n'


def main(argv=None):
    a = argparse.ArgumentParser(prog='ink-to-lean', description=__doc__.splitlines()[0])
    a.add_argument('bundle')
    a.add_argument('--names')
    a.add_argument('-o', '--output', required=True)
    a.add_argument('--lean', default='lean')
    a.add_argument('--check', action='store_true')
    a.add_argument('--statements')
    a.add_argument('--report')
    o = a.parse_args(argv)
    bundle = json.loads(Path(o.bundle).read_text())
    names = None
    if o.names:
        receipt = json.loads(Path(o.names).read_text())
        names = receipt.get('names', receipt)
    source, report = export(bundle, names)
    Path(o.output).write_text(source)
    result = {'exported': sum(r['status'] == 'exported' for r in report),
              'unsupported': [r for r in report if r['status'] != 'exported']}
    if o.check:
        code, errors, _ = check(o.lean, o.output)
        failed = sorted(failing_theorems(source, errors))
        result['lean'] = {'errors': len(errors), 'proof_failures': failed}
        for r in report:
            if r['status'] == 'exported':
                r['lean'] = 'failed' if ident(r['law']) in failed else 'proved'
        if o.statements:
            Path(o.statements).write_text(with_sorry(source, set(failed)))
    if o.report:
        Path(o.report).write_text(json.dumps(report, indent=1) + '\n')
    print(json.dumps(result))
    return 0


if __name__ == '__main__':
    sys.exit(main())
