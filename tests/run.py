#!/usr/bin/env python3

# run the gaz tests.  from the top of the tree:
#
#   $ python3 tests/run.py            # all tests
#   $ python3 tests/run.py sha256     # just one
#
# each tests/NAME.scm has a `main` that prints its results.  the test
# passes when
#   1) `gaz -eval` prints exactly what is in tests/NAME.exp, and
#   2) `gaz` compiles the file (to LLVM) without complaint.
#
# use -u to (re)write the .exp files from the evaluator's output.

import os
import re
import subprocess
import sys

here = os.path.dirname(os.path.abspath(__file__))
top = os.path.dirname(here)
gaz = os.path.join(top, 'gaz')

ansi = re.compile(r'\x1b\[[0-9;]*m')

def run(args):
    p = subprocess.run([gaz] + args, cwd=top, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out = ansi.sub('', p.stdout.decode('utf8', 'replace'))
    err = ansi.sub('', p.stderr.decode('utf8', 'replace'))
    # the Irken runtime reports its tick count on exit.
    err = '\n'.join(l for l in err.split('\n') if not l.startswith('{total ticks:'))
    return p.returncode, out, err.strip()

def test(name, update):
    src = os.path.join('tests', name + '.scm')
    exp_path = os.path.join(here, name + '.exp')
    code, out, err = run(['-eval', src])
    if code != 0 or err:
        return 'eval failed (exit %d) %s' % (code, err)
    if update:
        open(exp_path, 'w').write(out)
    elif not os.path.exists(exp_path):
        return 'no .exp file (use -u to create it)'
    elif out != open(exp_path).read():
        return 'eval output differs from %s.exp' % (name,)
    code, out, err = run([src])
    ll = os.path.join(here, name + '.ll')
    if os.path.exists(ll):
        os.unlink(ll)
    if code != 0 or err or out:
        return 'compile failed (exit %d) %s' % (code, err or out)
    return None

def main():
    args = sys.argv[1:]
    update = '-u' in args
    names = [a for a in args if a != '-u']
    if not names:
        names = sorted(f[:-4] for f in os.listdir(here) if f.endswith('.scm'))
    if not os.path.exists(gaz):
        sys.exit('no gaz binary at %s: build it first' % (gaz,))
    failed = 0
    for name in names:
        why = test(name, update)
        if why is None:
            print('%-12s ok' % (name,))
        else:
            failed += 1
            print('%-12s FAILED: %s' % (name, why))
    print('%d tests, %d failed' % (len(names), failed))
    sys.exit(1 if failed else 0)

if __name__ == '__main__':
    main()
