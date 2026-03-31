// Branch[35906] Iterator.prototype.flatMap
// target: GetIteratorDirect(O) (= abrupt)
// taken: false side taken (not abrupt), so have to target true side
"use strict";
Iterator.prototype.flatMap(x => x);
