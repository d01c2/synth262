// Branch[7853] Record[ProxyExoticObject].Get
// target: GetMethod(handler, "get") (= undefined)
// taken: false side taken (has get trap), so have to target true side
"use strict";
-(new Proxy({}, { get() {} }));
