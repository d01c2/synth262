// Branch[19892] InstallErrorCause
// target: HasProperty(options, "cause") (= false)
// taken: true side taken (has property), so have to target false side
"use strict";
new EvalError(0, { cause: 0 });
