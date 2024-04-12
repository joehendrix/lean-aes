/-
This is a fairly close implementation of the FIPS-197 standard:
 http://csrc.nist.gov/publications/fips/fips197/fips-197.pdf
-/

-- Nk: Number of blocks in the key
-- Must be one of 4 (AES128), 6 (AES192), or 8 (AES256)
-- Aside from this line, no other code below needs to change for
-- implementing AES128, AES192, or AES256
import AES.Vec

abbrev AES128 : Nat := 4
abbrev AES192 := 6
abbrev AES256 := 8

-- Number of blocks and Number of rounds
abbrev Nb := 4

abbrev Nr (k : Nat) : Nat := 6 + k

@[reducible]
def AESKeySize k := k * 32

structure GF28 where
  value : UInt8

macro "<| x |>" : term => `(GF28.mk 2)

namespace GF28

def irreducible : BitVec 9 := (2^9 + 2^4 + 2^3 + 2 + 1 : Nat)

def pmod (x : BitVec m) (p : BitVec (n+1)) : BitVec n :=
  if h : m ≤ n then
    x.zeroExtend n
  else
    let g : n+1 ≤ m := Nat.lt_of_not_le h
    let d : BitVec m := p.zeroExtend' g <<< (m - (n+1))
    let x : BitVec m := if x.toNat.testBit (m-1) then x ^^^ d else x
    pmod (x.truncate (m-1)) p

def pmultAux (r x y : Nat) : Nat :=
  if y = 0 then
    r
  else
    let r := if y % 2 = 1 then r ^^^ x else r
    pmultAux r (x <<< 1) (y / 2)

def pmult (x : BitVec m) (y : BitVec n) : BitVec (m + n) := pmultAux 0 x.toNat y.toNat

protected def ofNat (x : Nat) : GF28 :=  { value := UInt8.ofNat (pmod (.ofNat x.lg2 x) irreducible).toNat }

instance : DecidableEq GF28 := fun ⟨x⟩ ⟨y⟩ =>
  if p : x = y then
    .isTrue (congrArg GF28.mk p)
  else
    .isFalse (p ∘ GF28.mk.inj)

instance : Inhabited GF28 where
  default := { value := 0 }

instance : OfNat GF28 n where
  ofNat :=  GF28.ofNat n

instance : ToString GF28 where
  toString x :=  "0x" ++ (Nat.toDigits 16 x.value.toNat).asString

protected def rotateRight (x : GF28) (i : Nat) : GF28 :=
  let l := x.value >>> (UInt8.ofNat i)
  let h := (x.value.toNat % (2^i)) <<< (8 - i)
  { value := UInt8.ofNat h + l }

instance : HShiftRight GF28 Nat GF28 where
  hShiftRight := GF28.rotateRight

protected def toFin (v : GF28) : Fin 256 := v.value.val

protected def toBV (x : GF28) : BitVec 8 := .ofNat 8 x.value.toNat
protected def ofBV (x : BitVec 8) : GF28 := { value := UInt8.ofNat x.toNat }

instance : Coe GF28 (Fin 256) where
  coe := GF28.toFin

protected def add (x y : GF28) : GF28 := { value := x.value ^^^ y.value }

protected def mul (x y : GF28) : GF28 := GF28.ofBV (pmod (pmult x.toBV y.toBV) irreducible)

instance : Xor GF28 where
  xor := GF28.add

instance : Add GF28 where
  add := GF28.add

instance : Mul GF28 where
  mul := GF28.mul

def powAux (r x : GF28) (y : Nat) : GF28 :=
  if y = 0 then
    r
  else
    let r := if y % 2 = 1 then r * x else r
    powAux r (x * x) (y / 2)
  termination_by y

protected def pow (x : GF28) (y : Nat) : GF28 := powAux 1 x y

instance : HPow GF28 Nat GF28 where
  hPow := GF28.pow

end GF28

def gf28Add (l : List GF28) : GF28 := l.foldl (init := 0) (· + ·)

def gf28Inverse (x : GF28) : GF28 := x ^ 254

-- Helper type definitions
abbrev State := Vec 4 (Vec Nb GF28)
abbrev RoundKey    := State

abbrev KeySchedule (r : Nat) := RoundKey × Vec (r - 1) RoundKey × RoundKey

def sbox : Vec 256 GF28 := #v[
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
  0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
  0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
  0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,

  0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
  0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
  0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
  0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,

  0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
  0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
  0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
  0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,

  0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
  0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
  0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
  0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
  ]


-- The affine transform and its inverse
def xformByte (b : GF28) : GF28 := gf28Add [b, (b >>> 4), (b >>> 5), (b >>> 6), (b >>> 7), c]
   where c : GF28 := 0x63

def xformByte' (b : GF28) : GF28 := gf28Add [(b >>> 2), (b >>> 5), (b >>> 7), d]
  where d : GF28 := 0x05

-- The SubByte transform and its inverse
def SubByte (b : GF28) : GF28 := xformByte (gf28Inverse b)
def InvSubByte (b : GF28) : GF28 := gf28Inverse (xformByte' b)

-- Variant of subbyte implemented with sbox
def SubByte' (b : GF28) : GF28 := sbox[b.toFin]

def SubBytes (state : State) : State := state.map (·.map SubByte')

def InvSubBytes (state : State) : State := state.map (·.map InvSubByte)

-- The ShiftRows transform and its inverse
def ShiftRows (state : State) : State := Vec.ofFn (fun i => state[i].rotateL i.val)

def InvShiftRows (state : State) : State := Vec.ofFn (fun i => state[i].rotateR i.val)

-- The MixColumns transform and its inverse
def MixColumns (state : State) : State := Vec.mmult m state
  where m := #v[#v[2, 3, 1, 1],
                #v[1, 2, 3, 1],
                #v[1, 1, 2, 3],
                #v[3, 1, 1, 2]]

def InvMixColumns (state : State) : State := Vec.mmult m state
  where m := #v[#v[0x0e, 0x0b, 0x0d, 0x09],
                #v[0x09, 0x0e, 0x0b, 0x0d],
                #v[0x0d, 0x09, 0x0e, 0x0b],
                #v[0x0b, 0x0d, 0x09, 0x0e]]

-- The AddRoundKey transform
def AddRoundKey (rk : RoundKey) (s : State) : State := rk ^^^ s

-- Key expansion
def Rcon (i : Nat) : Vec 4 GF28 := #v[(<| x |>) ^ (i-1), 0, 0, 0 ]

def SubWord (bs : Vec 4 GF28) : Vec 4 GF28 := bs.map SubByte'

def RotWord (a : Vec 4 GF28) := a.rotateL 1

def NextWord (k : Nat) (i : Nat) (prev : Vec 4 GF28) (old : Vec 4 GF28) : Vec 4 GF28 := old ^^^ mask
  where mask :=
    if i % k == 0 then
      SubWord (RotWord prev) ^^^ Rcon (i / k)
    else if k > 6 ∧ i % k == 4 then
      SubWord prev
    else
      prev

def ExpandKey {k : Nat} (k_pos : 1 ≤ k) (key : BitVec (AESKeySize k)) : KeySchedule (Nr k) :=
    (keys[0], keys.slice 1 (Nr k - 1), keys[Nr k])
  where kp : AESKeySize k = k * 4 * 8 := by simp [AESKeySize, Nat.mul_assoc]
        klb : k ≤ 4 * (Nr k + 1) := by unfold Nr; omega
        seed : Vec k (Vec 4 GF28) := key |>.cast kp |>.split (m := k * 4) (n := 8) |>.map GF28.ofBV |>.split
        keyWs : Vec (4 * (Nr k + 1)) (Vec Nb GF28) :=
          ofRange (motive := fun i => Vec i (Vec Nb GF28)) k (4 * (Nr k + 1)) klb seed fun i lb _ v =>
            let prev := v[i-1];
            let old  := v[i-k];
            v.push (NextWord k i prev old)
        keys : Vec (Nr k + 1) RoundKey := (Vec.split (n := 4) (Vec.cast (Nat.mul_comm ..) keyWs)).map (·.transpose)

def AESRound (rk : RoundKey) (s : State) : State := AddRoundKey rk (MixColumns (ShiftRows (SubBytes s)))
def AESFinalRound (rk : RoundKey) (s : State) := AddRoundKey rk (ShiftRows (SubBytes s))

def AESInvRound (rk : RoundKey) (s : State) : State := InvMixColumns (AddRoundKey rk (InvSubBytes (InvShiftRows s)))
def AESFinalInvRound (rk : RoundKey) (s : State) := AddRoundKey rk (InvSubBytes (InvShiftRows s))

def msgToState (msg : BitVec 128) : State :=
  msg |>.split (m := Nb * 4) (n := 8) |>.map GF28.ofBV |>.split |>.transpose
def stateToMsg (st : State) : BitVec 128 := st |>.transpose |>.join |>.map GF28.toBV |>.joinBV

abbrev Nk := AES128

def aesEncrypt (k : Nat := AES128) (kpos : 1 ≤ k := by decide) (pt : BitVec 128) (key : BitVec (AESKeySize k)) : BitVec 128 := Id.run do
  let (kInit, ks, kFinal) := ExpandKey kpos key
  let mut s := AddRoundKey kInit (msgToState pt)
  for rk in ks.value do
    s := AESRound rk s
  return stateToMsg (AESFinalRound kFinal s)

def aesDecrypt (k : Nat := AES128) (kpos : 1 ≤ k) (ct : BitVec 128) (key : BitVec (AESKeySize k)) : BitVec 128 := Id.run do
  let (kFinal, ks, kInit) := ExpandKey kpos key
  let mut s := AddRoundKey kInit (msgToState ct)
  for rk in ks.value.reverse do
    s := AESInvRound rk s
  return stateToMsg (AESFinalInvRound kFinal s)


#print stateToMsg

@[simp]
theorem msgToState_stateToMsg (s : State) : msgToState (stateToMsg s) = s := by
  admit
-- (msgToState
--            (stateToMsg

theorem decryptEncrypt (k : Nat) (kpos : 1 ≤ k) (pt : BitVec 128) (key : BitVec (AESKeySize k)) :
    aesDecrypt k kpos (aesEncrypt k kpos pt key) key = pt := by
  simp [aesEncrypt, aesDecrypt, Id.run, AESFinalRound]
  admit

/--
info: 0x3925841d02dc09fbdc118597196a0b32#128
-/
#guard_msgs in
#eval aesEncrypt AES128 (by decide) 0x3243f6a8885a308d313198a2e0370734 0x2b7e151628aed2a6abf7158809cf4f3c

/--
info: 0x69c4e0d86a7b0430d8cdb78070b4c55a#128
-/
#guard_msgs in
#eval aesEncrypt AES128 (by decide) 0x00112233445566778899aabbccddeeff 0x000102030405060708090a0b0c0d0e0f

def test (pt : BitVec 128) (key : BitVec (AESKeySize Nk)) : BitVec 128 :=
  aesDecrypt AES128 (by decide) (aesEncrypt AES128 (by decide) pt key) key

/--
info: 0x00112233445566778899aabbccddeeff#128
-/
#guard_msgs in
#eval test 0x00112233445566778899aabbccddeeff 0x000102030405060708090a0b0c0d0e0f

/-

// AES Encryption
aesEncrypt : ([128], [AESKeySize]) -> [128]
aesEncrypt (pt, key) = stateToMsg (AESFinalRound (kFinal, rounds ! 0))
  where   (kInit, ks, kFinal) = ExpandKey key
          state0 = AddRoundKey(kInit, msgToState pt)
          rounds = [state0] # [ AESRound (rk, s) | rk <- ks
                                                 | s <- rounds
                              ]

// AES Decryption
aesDecrypt : ([128], [AESKeySize]) -> [128]
aesDecrypt (ct, key) = stateToMsg (AESFinalInvRound (kFinal, rounds ! 0))
  where   (kFinal, ks, kInit) = ExpandKey key
          state0 = AddRoundKey(kInit, msgToState ct)
          rounds = [state0] # [ AESInvRound (rk, s)
                              | rk <- reverse ks
                              | s  <- rounds
                              ]


// Test runs:

// cryptol> aesEncrypt (0x3243f6a8885a308d313198a2e0370734,   \
//                      0x2b7e151628aed2a6abf7158809cf4f3c)
// 0x3925841d02dc09fbdc118597196a0b32
// cryptol> aesEncrypt (0x00112233445566778899aabbccddeeff,   \
//                      0x000102030405060708090a0b0c0d0e0f)
// 0x69c4e0d86a7b0430d8cdb78070b4c55a
property AESCorrect msg key = aesDecrypt (aesEncrypt (msg, key), key) == msg

testmsgs = [0x6bc1bee22e409f96e93d7e117393172a
           ,0xae2d8a571e03ac9c9eb76fac45af8e51
           ,0x30c81c46a35ce411e5fbc1191a0a52ef
           ,0xf69f2445df4f9b17ad2b417be66c3710]


// AES128 tests

testkey128 = 0x2b7e151628aed2a6abf7158809cf4f3c

testct128 = [0x3ad77bb40d7a3660a89ecaf32466ef97
            ,0xf5d3d58503b9699de785895a96fdbaaf
            ,0x43b1cd7f598ece23881b00e3ed030688
            ,0x7b0c785e27e8ad3f8223207104725dd4]

property testsPass = and [ aesEncrypt (msg, testkey128) == ct
                         | msg <- testmsgs | ct <- testct128 ]


// AES192 tests

// testkey192 = 0x8e73b0f7da0e6452c810f32b809079e562f8ead2522c6b7b

// testct192 = [0xbd334f1d6e45f25ff712a214571fa5cc
//             ,0x974104846d0ad3ad7734ecb3ecee4eef
//             ,0xef7afd2270e2e60adce0ba2face6444e
//             ,0x9a4b41ba738d6c72fb16691603c18e0e]

// property testsPass = and [ aesEncrypt (msg, testkey192) == ct
//                          | msg <- testmsgs | ct <- testct192 ]


// AES256 tests

// testkey256 = 0x603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4
// testct256 = [0xf3eed1bdb5d2a03c064b5a7e3db181f8
//             ,0x591ccb10d410ed26dc5ba74a31362870
//             ,0xb6ed21b99ca6f4f9f153e7b1beafed1d
//             ,0x23304b7a39f9f3ff067d8d8f9e24ecc7]

// property testsPass = and [ aesEncrypt (msg, testkey256) == ct
//                          | msg <- testmsgs | ct <- testct256 ]
-/
