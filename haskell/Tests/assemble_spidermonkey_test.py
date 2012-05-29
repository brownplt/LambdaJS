#!/usr/bin/env python
import sys, os

# Testing plan:
#   - Don't mess with Rhino.
#   - Define a delta operator for print, that displays the string in Scheme.
#   - Compare stdout from Rhino to stdout from Redex.  If they are equal, win.
#
# Possible failures:
#   - Desugaring doesn't work.
#   - Redex does not reduce to a unique value or error.  (Even if the output is
#     identical, we fail if Redex doesn't reduce to a value or error.)

j = os.path.join

if len(sys.argv) < 2:
    print "Usage: assemble_spidermonkey_test.py pathToTest"
    sys.exit()

opath = sys.argv[1]

path, fname = os.path.split(opath)
basename, testdirname = os.path.split(path)

print open(j("SpiderMonkey", "shell.js")).read()
print open(j(basename, "shell.js")).read()
print open(j(path, "shell.js")).read()
print open(opath).read()


