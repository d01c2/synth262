"use strict";
var [ x ] = { [ Symbol . iterator ] : async function * ( ) { yield * { [ Symbol . iterator ] : async function * ( ) { yield ; } } ; } } ; 
