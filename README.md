# Idris backend for Malfunction

Compiles Idris to [Malfunction](https://github.com/stedolan/malfunction).

It seems to go pretty fast:
    
    $ idris pythag.idr -o pythag-idris
    $ idris pythag.idr --codegen malfunction -o pythag-malfunction
    
    $ time ./pythag-idris  > /dev/null
   
    real    0m4.548s
    user    0m4.528s
    sys     0m0.016s
    
    $ time ./pythag-malfunction  > /dev/null
    
    real    0m0.654s
    user    0m0.652s
    sys     0m0.000s

Tested on:
* Ubuntu `16.04.4 LTS 64-bit`
* Intel® Core™ i5-2500 CPU @ 3.30GHz × 4 
* 8 GB RAM
* Idris `1.2.0`
* Malfunction `v0.2.1`
* OCaml `4.05.0+flambda`
