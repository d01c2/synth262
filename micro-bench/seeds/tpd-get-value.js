// Branch[841] ToPropertyDescriptor
// target: Get(Obj, "value") (abrupt)
// taken: false side taken (not abrupt), so have to target true side
"use strict";
Reflect.defineProperty({}, 0, { value: 1 });
