// Branch[8124] INTRINSICS.Proxy.Construct
// target: GetMethod(handler, "construct") (abrupt)
// taken: false side taken (not abrupt), so have to target true side
"use strict";
new (new Proxy(class {}, {}));
