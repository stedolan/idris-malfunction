-- Example stolen from https://github.com/edwinb/idris-php, 
-- with the numbers changed to make it run for longer

module Main

-- this speeds up the Idris native version a bit.
%flag C "-O3"


pythag : Int -> List (Int, Int, Int)
pythag max = [(x, y, z) | z <- [1..max], y <- [1..z], x <- [1..y],
                              x * x + y *y == z * z]

main : IO ()
main = print (pythag 500)
