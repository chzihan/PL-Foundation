{-# OPTIONS -fglasgow-exts #-}

-- Generated by Alonzo

module Bool where
import RTS
import qualified RTP
name1 = "Bool"

data T1 = C2
        | C3
d1 = ()
name2 = "true"
name3 = "false"
name5 = "if_then_else_"
d5 = d5_1
  where d5_1 _ (Bool.C2) v0 v1 = cast v0
        d5_1 a b c d = cast d5_2 a b c d
        d5_2 _ (Bool.C3) v0 v1 = cast v1
