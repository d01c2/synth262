"use strict";
Array . prototype . shift . call ( ( new Proxy ( [ ] , { set ( ) { return 1 ; } } ) ) ) ; 
