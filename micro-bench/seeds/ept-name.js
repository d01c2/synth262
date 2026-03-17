// Branch[19599] INTRINSICS.Error.prototype.toString
// target: Get(O, "name") (= undefined)
// taken: true side taken (undefined), so have to target false side
"use strict";
Error.prototype.toString.call({});
