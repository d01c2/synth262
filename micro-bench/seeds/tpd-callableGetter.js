// Branch[873] ToPropertyDescriptor
// target: IsCallable(getter) after Get(Obj, "get") (= not callable)
// taken: false side taken (callable), so have to target true side
"use strict";
Object.create([], { x: { get: x => x } });
