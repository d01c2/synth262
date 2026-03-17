// Branch[31936] GetSetRecord
// target: Get(obj, "has") (with IsCallable)
// taken: true side taken (not callable), so have to target false side
"use strict";
Set.prototype.union.call(new Set, { size: 0 });
