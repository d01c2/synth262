// Branch[35949] Iterator.prototype.forEach
// target: IteratorStepValue(iterated) value == ~done~
// taken: true side taken (done), so have to target false side
"use strict";
Iterator.prototype.forEach.call({ next: async x => x }, x => x);
