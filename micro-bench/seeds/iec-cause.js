// Branch[19892] InstallErrorCause
// target: HasProperty(options, "cause")
// taken: false side taken, so have to target true side
"use strict";
new Error(0, {});
