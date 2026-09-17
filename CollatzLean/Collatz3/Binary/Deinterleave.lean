import CollatzLean.Collatz3.Binary.AlternatingWeight

/-!
# Collatz3 Binary: even / odd position deinterleave

LSB-first binary word を、偶数位置と奇数位置の二本の binary word に分離する。

primitive は `evenBits` / `oddBits` と通常の one-count だけに留める。
探索段階で使った圧縮整数は、それぞれの deinterleaved word の `valueLSB` として導く。
-/

namespace Collatz3
namespace Binary

mutual
  /-- LSB から数えて偶数位置 `0,2,4,...` の bit を順序を保って抜き出す。 -/
  def evenBits : List Bool → List Bool
    | [] => []
    | b :: bs => b :: oddBits bs

  /-- LSB から数えて奇数位置 `1,3,5,...` の bit を順序を保って抜き出す。 -/
  def oddBits : List Bool → List Bool
    | [] => []
    | _ :: bs => evenBits bs
end

@[simp] theorem evenBits_nil : evenBits [] = [] := rfl
@[simp] theorem oddBits_nil : oddBits [] = [] := rfl

@[simp] theorem evenBits_cons (b : Bool) (bs : List Bool) :
    evenBits (b :: bs) = b :: oddBits bs := rfl

@[simp] theorem oddBits_cons (b : Bool) (bs : List Bool) :
    oddBits (b :: bs) = evenBits bs := rfl

/-- binary word に含まれる `1` の総数。 -/
def oneCount : List Bool → ℕ
  | [] => 0
  | b :: bs => bitValue b + oneCount bs

@[simp] theorem oneCount_nil : oneCount [] = 0 := rfl
@[simp] theorem oneCount_cons (b : Bool) (bs : List Bool) :
    oneCount (b :: bs) = bitValue b + oneCount bs := rfl

/--
deinterleave 後の one-count は、元の alternating weight と exact に一致する。
二本を同時に示すことで mutual recursion の位相交換をそのまま吸収する。
-/
theorem oneCount_deinterleave (bits : List Bool) :
    oneCount (evenBits bits) = evenOneCount bits ∧
      oneCount (oddBits bits) = oddOneCount bits := by
  induction bits with
  | nil =>
      simp
  | cons b bs ih =>
      rcases ih with ⟨hEven, hOdd⟩
      constructor
      · simp [hOdd]
      · simp [hEven]

/-- 偶数位置を圧縮して得る自然数。 -/
def evenCompressedValue (bits : List Bool) : ℕ :=
  valueLSB (evenBits bits)

/-- 奇数位置を圧縮して得る自然数。 -/
def oddCompressedValue (bits : List Bool) : ℕ :=
  valueLSB (oddBits bits)

/-- 偶数位置圧縮語の `1` 数は even alternating weight。 -/
theorem oneCount_evenBits (bits : List Bool) :
    oneCount (evenBits bits) = evenOneCount bits :=
  (oneCount_deinterleave bits).1

/-- 奇数位置圧縮語の `1` 数は odd alternating weight。 -/
theorem oneCount_oddBits (bits : List Bool) :
    oneCount (oddBits bits) = oddOneCount bits :=
  (oneCount_deinterleave bits).2

end Binary
end Collatz3
