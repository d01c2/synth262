// Branch[813] ToPropertyDescriptor
// target: Get(Obj, "enumerable") (abrupt)
// taken: false side taken (not abrupt), so have to target true side
"use strict";
Object.defineProperty({}, '', {});
