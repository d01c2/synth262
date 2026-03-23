"use strict";
; 1 ^ delete ( new Proxy ( { } , { deleteProperty ( ) { return 1 ; } } ) ) . iterator ; 
