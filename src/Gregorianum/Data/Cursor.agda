module Gregorianum.Data.Cursor where

open import Gregorianum.Data.Cursor.Base public

pattern first = zero
pattern second = suc first
pattern third = suc second
pattern fourth = suc third
pattern fifth = suc fourth
pattern sixth = suc fifth
pattern seventh = suc sixth
pattern eighth = suc seventh
pattern ninth = suc eighth
pattern tenth = suc ninth
pattern eleventh = suc tenth
pattern twelfth = suc eleventh
pattern thirteenth = suc twelfth
pattern fourteenth = suc thirteenth
pattern fifteenth = suc fourteenth
pattern sixteenth = suc fifteenth
pattern seventeenth = suc sixteenth
pattern eighteenth = suc seventeenth
pattern nineteenth = suc eighteenth
pattern twentieth = suc nineteenth
pattern twenty-first = suc twentieth
pattern twenty-second = suc twenty-first
pattern twenty-third = suc twenty-second
pattern twenty-fourth = suc twenty-third
pattern twenty-fifth = suc twenty-fourth
pattern twenty-sixth = suc twenty-fifth
pattern twenty-seventh = suc twenty-sixth
pattern twenty-eighth = suc twenty-seventh
pattern twenty-ninth = suc twenty-eighth
pattern thirtieth = suc twenty-ninth
pattern thirty-first = suc thirtieth

pattern suc⁴ x = suc (suc (suc (suc x)))

pattern suc¹² x = suc⁴ (suc⁴ (suc⁴ x))

private
  pattern suc⁵ x = suc (suc⁴ x)

pattern suc²⁵ x = suc⁵ (suc⁵ (suc⁵ (suc⁵ (suc⁵ x))))
