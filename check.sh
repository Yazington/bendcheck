#!/bin/sh
# bendcheck's checks: the test suite, then the mutation tests.
set -u
cd "$(dirname "$0")"
python3 tests/run.py || exit 1
python3 tests/mutants.py || exit 1
echo "ALL CHECKS PASSED"
