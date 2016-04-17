module Main

import Crypto.Data

failMessage : String -> String -> String
failMessage expected actual =
  unlines [ "    FAIL!"
          , "Expected: " ++ expected
          , "  Actual: " ++ actual
          ]

test : String -> Maybe String -> (Bool, String)
test expected maybeActual =
  let actual = fromMaybe "(Nothing)" maybeActual in
    if expected == actual
      then (True, "PASS")
      else (False, failMessage expected actual)

testIO : String -> Maybe String -> IO ()
testIO expected maybeActual =
  let (_, msg) = test expected maybeActual in
    putStrLn msg

test1 : IO ()
test1 =
  let input = "49276d206b696c6c696e6720796f757220627261696e206c696b65206120706f69736f6e6f7573206d757368726f6f6d"
      expected = "SSdtIGtpbGxpbmcgeW91ciBicmFpbiBsaWtlIGEgcG9pc29ub3VzIG11c2hyb29t" in
    testIO expected (hexToBase64 input)

test2 : IO ()
test2 =
let inputA = "1c0111001f010100061a024b53535009181c"
    inputB = "686974207468652062756c6c277320657965"
    expected = "746865206B696420646F6E277420706C6179" in
  testIO expected (fixedXOR inputA inputB)

main : IO ()
main =
  do putStrLn "Challenge 1:"
     test1
     putStrLn ""
     putStrLn "Challenge 2:"
     test2
