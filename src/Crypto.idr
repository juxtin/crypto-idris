module Main

import Crypto.Data

test1 : IO ()
test1 =
  let test = "49276d206b696c6c696e6720796f757220627261696e206c696b65206120706f69736f6e6f7573206d757368726f6f6d" in
    case hexToBase64 test of
      Nothing => putStrLn "Unable to parse the challenge 1 input!"
      Just b64 => putStrLn b64

test2 : IO ()
test2 =
let inputs = ( "1c0111001f010100061a024b53535009181c"
             , "686974207468652062756c6c277320657965") in
  case (uncurry fixedXOR) inputs of
    Nothing => putStrLn "Unable to process the challenge 2 inputs!"
    Just hex => putStrLn hex

main : IO ()
main =
  do putStrLn "Result of challenge 1:"
     test1
     putStrLn ""
     putStrLn "Result of challenge 2:"
     test2
