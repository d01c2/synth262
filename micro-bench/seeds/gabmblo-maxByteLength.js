// Branch[33008] GetArrayBufferMaxByteLengthOption
// target: Get(options, "maxByteLength") (= undefined)
// taken: true side taken (undefined), so have to target false side
"use strict";
new ArrayBuffer(0, {});
