"use strict";
( new Proxy ( { } , { defineProperty : x => x } ) ) . x ??= 1 ; 
