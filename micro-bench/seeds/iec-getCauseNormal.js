// Branch[19895] InstallErrorCause
// target: Get(options, "cause") (= normal completion)
// taken: true side taken (abrupt via throwing getter), so have to target false side
"use strict";
new EvalError(0, { get cause() { x; } });
