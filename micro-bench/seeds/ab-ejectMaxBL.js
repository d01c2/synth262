// Branch[33008] GetArrayBufferMaxByteLengthOption
// target: Get(options, "maxByteLength") (= undefined)
// taken: false side taken (has maxByteLength), so have to target true side
"use strict";
new ArrayBuffer(0, { maxByteLength: 1 });
