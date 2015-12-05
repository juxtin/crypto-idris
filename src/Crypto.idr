module Main

import Crypto.Data

test1 : IO ()
test1 =
  let test = "49276d206b696c6c696e6720796f757220627261696e206c696b65206120706f69736f6e6f7573206d757368726f6f6d" in
    case hexToBase64 test of
      Nothing => putStrLn "Unable to parse the test hex string!"
      Just b64 => putStrLn b64

main : IO ()
main =
  do putStrLn "Result of challenge 1:"
     test1
