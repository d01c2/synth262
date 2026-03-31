// Branch[36055] Iterator.prototype.reduce
// target: GetIteratorDirect(O) (= abrupt)
// taken: false side taken (not abrupt), so have to target true side
"use strict";
Iterator.prototype.reduce(x => x);
