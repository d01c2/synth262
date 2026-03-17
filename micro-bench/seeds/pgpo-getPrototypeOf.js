// Branch[7460] INTRINSICS.Proxy.GetPrototypeOf
// target: GetMethod(handler, "getPrototypeOf") (callable value)
// taken: true side taken (callable), so have to target false side
"use strict";
for (x in (new Proxy({}, {})));
