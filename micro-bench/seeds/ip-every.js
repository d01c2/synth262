// Branch[35659] Iterator.prototype.every
// target: GetIteratorDirect(O) (= abrupt)
// taken: false side taken (not abrupt), so have to target true side
"use strict";
Iterator.prototype.every(x => x);
