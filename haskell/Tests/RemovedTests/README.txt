PERMANENTLY REMOVED:
----------------------
Spidermonkey/
  Arrays/
    regress-130451.js - uses eval
  ExecutionContexts/
  Expressions/
    11.6.1-1.js - uses eval
    11.9.6-1.js - uses eval to check that its return val is 'undefined'
  Function/
    call-001 - eval
  Operators/
    11.13.1-001.js - uses eval
    order-01.js - more eval plox. can potentially be worked out, as it's
                  a very simple use of it.
  Statements/
    regress-157509.js - eval
    regress-194364.js - eval
    regress-302439.js - program too complex for Rhino
                        not this is not a contrived example and maybe
                        we shuld run it
    regress-324650.js - program too complex for Rhino
    regress-444979.js - too complx for Rhino
    regress-74474-002.js - too complex for Rhino
    regress-74474-003.js - cmplx for Rhino
    regress-83532-002.js - evalbomb
    regress-121744.js - has warning not to run it after 2002

TEMPORARILY REMOVED:
-----------------------
ExecutionContexts:
    10.3.1-1.js - TMP: relies on arguments[0] being aliased to the formal var

Exceptions
  - *pending DontDelete, ReadOnly, DontEnum
  - *binding-001.js: throw a ReferenceError for undeclared global variables.
  - *regress-181654: String.prototype.search
  - *regress-95101: String.prototype.search
FunExpr
  - *fe-001.js: lifting order | Details of Rhino / SpiderMonkey

Function
  - *15.3.4.3-1.js: dereffing arguments twice | apply details
  - *15.3.4.4-1.js: toObject received undefined | call not implemented
  - *regress-313570: something about prototype chains | ReadOnly
  - *regress-85880: something about arguments
  - *scope-001/002: opIN. maybe remove?
Number
  - *15.7.4.5-2: toFixed fail. boring!

Regress
  - *regress-419152: fix up array to have "" instead of "undefined"

