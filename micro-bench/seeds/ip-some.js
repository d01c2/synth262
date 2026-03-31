// Branch[36124] Iterator.prototype.some
// target: IteratorStepValue(iterated) (= abrupt)
// taken: true side taken (abrupt), so have to target false side
"use strict";
Iterator.prototype.some(x => x);
