// Branch[36075] Iterator.prototype.reduce
// target: IteratorStepValue(iterated) in loop (= abrupt)
// taken: true side taken (abrupt), so have to target false side
"use strict";
Iterator.prototype.reduce(x => x, 0);
