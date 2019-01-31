;buildInfoPackage: chisel3, version: 3.2-SNAPSHOT, scalaVersion: 2.11.12, sbtVersion: 1.2.7
circuit Compute3Vec : 
  module Compute3Vec : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip a : UInt<32>[5], flip b : UInt<32>[5], out : UInt<32>, done : UInt<1>}
    
    reg cReg : UInt<32>, clock with : (reset => (reset, UInt<32>("h064"))) @[Loop.scala 80:21]
    reg pipe0Reg : UInt<32>, clock with : (reset => (reset, UInt<32>("h00"))) @[Loop.scala 81:25]
    reg loopIndex : UInt<32>, clock with : (reset => (reset, UInt<32>("h00"))) @[Loop.scala 110:26]
    node _T = lt(loopIndex, UInt<3>("h05")) @[Loop.scala 111:19]
    loop _T : @[Loop.scala 111:32]
      node _T_1 = or(loopIndex, UInt<3>("h00"))
      node _T_2 = bits(_T_1, 2, 0)
      node _T_3 = or(loopIndex, UInt<3>("h00"))
      node _T_4 = bits(_T_3, 2, 0)
      node _T_5 = mul(io.a[_T_2], io.b[_T_4]) @[Loop.scala 113:33]
      pipe0Reg <= _T_5 @[Loop.scala 113:14]
      node _T_6 = add(cReg, pipe0Reg) @[Loop.scala 114:18]
      node _T_7 = tail(_T_6, 1) @[Loop.scala 114:18]
      cReg <= _T_7 @[Loop.scala 114:10]
      node _T_8 = add(loopIndex, UInt<1>("h01")) @[Loop.scala 115:28]
      node _T_9 = tail(_T_8, 1) @[Loop.scala 115:28]
      loopIndex <= _T_9 @[Loop.scala 115:15]
      skip @[Loop.scala 111:32]
    node _T_10 = eq(loopIndex, UInt<3>("h05")) @[Loop.scala 118:25]
    io.done <= _T_10 @[Loop.scala 118:11]
    io.out <= cReg @[Loop.scala 138:10]
    
