;buildInfoPackage: chisel3, version: 3.2-SNAPSHOT, scalaVersion: 2.11.12, sbtVersion: 1.2.7
circuit Compute3Mem : 
  module Compute3Mem : 
    input clock : Clock
    input reset : UInt<1>
    output io : {flip a : UInt<32>[5], flip b : UInt<32>[5], flip c : UInt<32>[5], out : UInt<32>, done : UInt<1>}
    
    smem ramA : UInt<32>[16] @[Loop.scala 150:25]
    smem ramB : UInt<32>[16] @[Loop.scala 151:25]
    smem ramC : UInt<32>[16] @[Loop.scala 152:25]
    reg idx : UInt<32>, clock with : (reset => (reset, UInt<32>("h00"))) @[Loop.scala 153:20]
    reg loopIndex0 : UInt<32>, clock with : (reset => (reset, UInt<32>("h00"))) @[Loop.scala 183:27]
    reg loopIndex0Delay : UInt, clock @[Loop.scala 184:32]
    loopIndex0Delay <= loopIndex0 @[Loop.scala 184:32]
    node loop0Done = eq(loopIndex0Delay, UInt<3>("h05")) @[Loop.scala 185:36]
    node _T = lt(loopIndex0, UInt<3>("h05")) @[Loop.scala 187:20]
    loop _T : @[Loop.scala 187:33]
      node _T_1 = bits(loopIndex0, 2, 0)
      node _T_2 = bits(loopIndex0, 3, 0)
      write mport _T_3 = ramA[_T_2], clock
      _T_3 <= io.a[_T_1]
      node _T_4 = bits(loopIndex0, 2, 0)
      node _T_5 = bits(loopIndex0, 3, 0)
      write mport _T_6 = ramB[_T_5], clock
      _T_6 <= io.b[_T_4]
      node _T_7 = bits(loopIndex0, 2, 0)
      node _T_8 = bits(loopIndex0, 3, 0)
      write mport _T_9 = ramC[_T_8], clock
      _T_9 <= io.c[_T_7]
      node _T_10 = add(loopIndex0, UInt<1>("h01")) @[Loop.scala 191:30]
      node _T_11 = tail(_T_10, 1) @[Loop.scala 191:30]
      loopIndex0 <= _T_11 @[Loop.scala 191:16]
      skip @[Loop.scala 187:33]
    reg cReg : UInt<32>, clock with : (reset => (reset, UInt<32>("h064"))) @[Loop.scala 194:21]
    reg pipe0Reg : UInt<32>, clock with : (reset => (reset, UInt<32>("h00"))) @[Loop.scala 195:25]
    reg loopIndex : UInt<32>, clock with : (reset => (reset, UInt<32>("h00"))) @[Loop.scala 232:26]
    reg loopIndexDelay : UInt, clock @[Loop.scala 233:31]
    loopIndexDelay <= loopIndex @[Loop.scala 233:31]
    node loop1Done = eq(loopIndexDelay, UInt<3>("h05")) @[Loop.scala 234:35]
    node _T_12 = lt(loopIndex, UInt<3>("h05")) @[Loop.scala 236:19]
    node _T_13 = and(_T_12, loop0Done) @[Loop.scala 236:31]
    loop _T_13 : @[Loop.scala 236:45]
      node _T_14 = bits(loopIndex, 3, 0) @[Loop.scala 237:22]
      read mport _T_15 = ramA[_T_14], clock @[Loop.scala 237:22]
      node _T_16 = bits(loopIndex, 3, 0) @[Loop.scala 238:22]
      read mport _T_17 = ramB[_T_16], clock @[Loop.scala 238:22]
      node _T_18 = bits(loopIndex, 3, 0) @[Loop.scala 239:22]
      read mport _T_19 = ramC[_T_18], clock @[Loop.scala 239:22]
      node _T_20 = mul(_T_15, _T_17) @[Loop.scala 240:19]
      pipe0Reg <= _T_20 @[Loop.scala 240:14]
      node _T_21 = add(_T_19, pipe0Reg) @[Loop.scala 241:29]
      node _T_22 = tail(_T_21, 1) @[Loop.scala 241:29]
      node _T_23 = bits(loopIndex, 3, 0)
      write mport _T_24 = ramC[_T_23], clock
      _T_24 <= _T_22
      node _T_25 = add(loopIndex, UInt<1>("h01")) @[Loop.scala 242:28]
      node _T_26 = tail(_T_25, 1) @[Loop.scala 242:28]
      loopIndex <= _T_26 @[Loop.scala 242:15]
      skip @[Loop.scala 236:45]
    reg loopIndex2 : UInt<32>, clock with : (reset => (reset, UInt<32>("h00"))) @[Loop.scala 273:27]
    reg loopIndex2Delay : UInt, clock @[Loop.scala 274:32]
    loopIndex2Delay <= loopIndex2 @[Loop.scala 274:32]
    node loop2Done = eq(loopIndex2Delay, UInt<3>("h05")) @[Loop.scala 275:36]
    node _T_27 = lt(loopIndex2, UInt<3>("h05")) @[Loop.scala 277:20]
    node _T_28 = and(_T_27, loop1Done) @[Loop.scala 277:32]
    loop _T_28 : @[Loop.scala 277:46]
      node _T_29 = bits(loopIndex2, 3, 0) @[Loop.scala 278:22]
      read mport _T_30 = ramC[_T_29], clock @[Loop.scala 278:22]
      node _T_31 = add(cReg, _T_30) @[Loop.scala 279:18]
      node _T_32 = tail(_T_31, 1) @[Loop.scala 279:18]
      cReg <= _T_32 @[Loop.scala 279:10]
      node _T_33 = add(loopIndex2, UInt<1>("h01")) @[Loop.scala 280:30]
      node _T_34 = tail(_T_33, 1) @[Loop.scala 280:30]
      loopIndex2 <= _T_34 @[Loop.scala 280:16]
      skip @[Loop.scala 277:46]
    io.done <= loop2Done @[Loop.scala 284:11]
    io.out <= cReg @[Loop.scala 285:10]
    
