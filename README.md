# Idris backend for Malfunction

Compiles Idris to [Malfunction](https://github.com/stedolan/malfunction)

It seems to go pretty fast:

    $ idris pythag.idr -o pythag-idris
    $ idris pythag.idr --codegen malfunction -o pythag-malfunction
    $ time ./pythag-idris  > /dev/null
    
    real    0m13.102s
    user    0m13.084s
    sys     0m0.004s
    $ time ./pythag-malfunction  > /dev/null
    
    real    0m1.096s
    user    0m1.092s
    sys     0m0.000s
    $ 
