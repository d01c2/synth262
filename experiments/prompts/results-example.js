// Branch[1277]:T : String.fromCharCode.call(0, 0n );
// Branch[1277]:F : new Uint16Array([ , ] );
// Branch[1277]   : Test262 covered false branch with "test262/test/language/literals/string/S7.8.4_A5.1_T1.js"

// > [!NOTE]
// > loc: [ToUint16 step 1](https://tc39.es/ecma262/2025/#sec-touint16)
// > uncovered: ToNumber return abrupt completion case
// > isValid: true
// > - String.fromCharCode(...codeUnits)의 codeUnits로 접근 가능
// > - argument에 Symbol이나 BigInt 값을 넣어주면 됨
// > - ToUint16Array constructor로도 접근 가능해 보이나 SetValueInBuffer에서 type이 Uint16라서 (BigInt가 아님) number로 강제되어 도달 불가 (NumericToRawBytes 참고)
// > - test262에 String.fromCharCode의 argument에 symbol이나 BigInt 넣어주는 케이스 없음

// A0: uncovered branch가 위치하는 algo와 step (2.4s, not covered)
var obj = { valueOf: function () { throw new Test262Error(); } };
new Uint16Array([obj]);

// A1: A0 + 해당 알고리즘까지 도달하는 path들 (2.4s, covered)
var threw = false;
try { String.fromCharCode({ valueOf: function () { throw new Test262Error(); } }); } catch (e) { threw = e instanceof Test262Error; } if (!threw) throw new Error();

// A2: A1 + uncovered branch의 반대쪽 branch을 지나는 프로그램 (1.3s, covered)
var poison = { valueOf: function () { throw new Test262Error(); } };
String.fromCharCode(poison);

// A3: A2 + 반대쪽 branch를 지나는 프로그램에서 localization된 AST (1.2s, covered)
String.fromCharCode({ valueOf() { throw new Test262Error(); } });
