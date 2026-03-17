// Branch[838] ToPropertyDescriptor
// target: HasProperty(Obj, "value")
// taken: false side taken, so have to target true side
"use strict";
Reflect.defineProperty({}, 0, {});
