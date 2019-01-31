// See LICENSE for license details.

package loop

import collection._

import firrtl._
import firrtl.ir._
import firrtl.PrimOps.{Eq, Not, And, Or}
import firrtl.{Transform, HighForm, CircuitState, Utils}
import firrtl.Mappers._
import firrtl.Utils._

object LoopTransform extends Transform {
  def inputForm = HighForm
  def outputForm = HighForm
  private def looptransform(renames: RenameMap)(s: Statement): Statement = {
    val defUseMap = mutable.HashMap[String, Seq[String]]()
    val tmpConMap = mutable.HashMap[String, String]()
    val conMap = mutable.HashMap[(String, String), String]()
    val schedUnits = mutable.HashMap[String, (Int, Statement)]()
    val conUnits = mutable.HashSet[String]()
    // 0: read, 1: write
    val memUnits = mutable.HashMap[String, (String, String, Int)]()
    val memWMap = mutable.HashMap[String, String]()
    val mPortMap = mutable.HashMap[String, Statement]()
    val dfEdges = mutable.HashMap[(String, String), Int]()
    val ordEdges = mutable.HashSet[(String, String)]()
    val loopStages = mutable.HashMap[Int, Seq[String]]()
    var clk = Seq[Expression]()
    var rst = Seq[Expression]()

    def getRef(set: mutable.HashSet[String])
              (e: Expression): Expression = {
      e match {
        case Reference(name, _) =>
          set += name
        //case SubAccess(expr, index, _) =>
        case SubField(expr, field, _) =>
          set += field
          e map getRef(set)
        case _ =>
          e map getRef(set)
      }
      e
    }

    def checkConnect(s: Statement): Statement = {
      val useSet = mutable.HashSet[String]()
      val defSet = mutable.HashSet[String]()

      // Note that we visit Statements of the loop body in order
      s match {
        case c: Connect =>
          getRef(defSet)(c.loc)
          getRef(useSet)(c.expr)
          println("defSet: " + defSet)
          println("useSet: " + useSet)
          // Avoid literals
          if (!useSet.isEmpty) {
            val use = if (useSet.size > 1) {
              useSet.hashCode.toHexString
            }
            else {
              useSet.head
            }
            if (memUnits.contains(defSet.head)) {
              memWMap += (use -> defSet.head)
            }
            conUnits += defSet.head
            tmpConMap += (defSet.head -> use)

            for ((s, _) <- schedUnits) {
              val check = hasChild(s, defSet.head, 0)
              if (check._1 == true && check._2 == 0) {
                println("TEST " + s + " " + defSet.head + " " + check)
                ordEdges += ((use, s))
              }
            }
            schedUnits += (use -> (0, c))
          }
        case n: DefNode =>
          getRef(useSet)(n.value)
          useSet.foreach(u =>
            if (tmpConMap.contains(u)) {
              conMap += ((n.name, u) -> tmpConMap(u))
              tmpConMap -= u
            }
          )

          defUseMap += (n.name -> useSet.toSeq)
        case m: CDefMPort =>          
          val addr = m.exps.head match {
            case Reference(name, _) => name
            case _ => ""
          }
          val dir = m.direction match {
            case MRead => 0
            case MWrite => 1
            case _ => 2
          }
          mPortMap += (m.name -> m)
          memUnits += (m.name -> (m.mem, addr, dir))
          defUseMap += (m.name -> Seq(addr))
          schedUnits += (m.name -> (0, m))
        case _ =>
          s map checkConnect
      }
      s
    }

    def hasChild(parent: String, child: String, latency: Int): (Boolean, Int) = {
      if (parent == child) {
        (true, latency)
      }
      else if (!defUseMap.contains(parent)) {
        (false, latency)
      }
      else {
        if (defUseMap(parent).contains(child)) {
          // memory node is assumed to have a delay of 1 (for now)
          if (memUnits.contains(child)) {
            (true, latency + 1)
          }
          else {
            (true, latency)
          }
        }
        else {
          val ret = defUseMap(parent).map(u =>
            if (conUnits.contains(u) && conMap.contains((parent, u))) {
              hasChild(conMap((parent, u)), child, latency + 1)
            }
            else {
              hasChild(u, child, latency)
            }
          ).filter(x => x._1 == true)

          if (ret.isEmpty) {
            (false, latency)
          }
          else {
            ret.head
          }

        }
      }
    }

    // TODO: check for memory dependency
    def buildDepEdges(): Unit = {
      val names = schedUnits.map({case (x, (_, _)) => x })
      val edges = for (x <- names; y <- names; if (x != y)) yield (x, y)
      edges.foreach(e => {
        val ret = hasChild(e._1, e._2, 0)
        if (ret._1) {
          dfEdges += (e -> ret._2)
        }
      })
    }

    def removeSchedStmts(s: Statement): Statement = {
      s match {
        case c: Connect  => EmptyStmt
        case m: CDefMPort => EmptyStmt
        case _ => s map removeSchedStmts
      }
    }

    def buildFSM(loopCond: Expression, oldBody: Statement): Statement = {
      // Definitely need an ILP solver here to simplify the following code
      // First round: establish latencies of several schedUnits based on
      // dataflow and memory dependencies
      for ((x, (_, _)) <- schedUnits;
           (y, (_, _)) <- schedUnits;
           if x != y) yield {
        if (dfEdges.contains((x, y))) {
          schedUnits(x) = (math.max(schedUnits(x)._1, schedUnits(y)._1 + dfEdges((x, y))), schedUnits(x)._2)
        }

        if (memWMap.contains(x)) {
          schedUnits(memWMap(x)) = (schedUnits(x)._1, schedUnits(memWMap(x))._2)
        }

      }
      // Second round: correct some schedUnits based on ordered edges
      for ((x, (_, _)) <- schedUnits;
           (y, (_, _)) <- schedUnits;
           if x != y) yield {
        if (ordEdges.contains(x, y)) {
          if (schedUnits(x)._1 < schedUnits(y)._1) {
            schedUnits(x) = (schedUnits(y)._1, schedUnits(x)._2)
          }
        }
      }

      for ((x, (state, stmt)) <- schedUnits) yield {
        if (!loopStages.contains(state)) {
          loopStages += (state -> Seq(x))
        }
        else {
          loopStages(state) = loopStages(state) ++ Seq(x)
        }
      }

      val nonSchedStmts = removeSchedStmts(oldBody)
      var fsmBlock = Seq[Statement]()

      var stages = Seq[DefRegister]()
      var stageTransformBlock = Seq[Statement]()

      // Provide unique loop name for each set of loop stage variables
      val loopNamePrefix = "loop_" + oldBody.serialize.hashCode.toHexString + "_"

      for (i <- 0 until loopStages.size) {
        val stage = DefRegister(NoInfo, loopNamePrefix + "stage" + i,
                                BoolType,
                                clk.head, rst.head,
                                zero)
        stages = stages ++ Seq(stage)
      }

      val stageBegin = DefRegister(NoInfo, loopNamePrefix + "stageBegin",
                                   BoolType, clk.head, rst.head, zero)
      val stageEnd = DefRegister(NoInfo, loopNamePrefix + "stageEnd",
                                 BoolType, clk.head, rst.head, zero)

      // (!stageBegin && loopCond)
      val initialLoopRunPred = DoPrim(And,
                                      Seq(DoPrim(Not,
                                                 Seq(WRef(stageBegin)),
                                                 Nil,
                                                 BoolType),
                                          loopCond),
                                      Nil,
                                      BoolType)
      // (stageEnd && loopCond)
      val successiveLoopRunPred = DoPrim(And,
                                         Seq(WRef(stageEnd),
                                             loopCond),
                                         Nil,
                                         BoolType)
      // (stageEnd && !loopCond)
      val loopDonePred = DoPrim(And,
                                Seq(WRef(stageEnd),
                                    DoPrim(Not,
                                           Seq(loopCond),
                                           Nil,
                                           BoolType)),
                                Nil,
                                BoolType)
      val stageBeginWhenStmt = Conditionally(NoInfo, initialLoopRunPred,
        Block(Seq(Connect(NoInfo, WRef(stageBegin), one))),
        Conditionally(NoInfo, loopDonePred,
          Block(Seq(Connect(NoInfo, WRef(stageBegin), zero))), EmptyStmt)
      )

      stageTransformBlock = stageTransformBlock ++
                            Seq(stageBeginWhenStmt)

      for (i <- 0 to loopStages.size) {
        val stageTfPred = if (i == 0) {
          // (!stageBegin && loopCond) || (stageEnd && loopCond)
          DoPrim(Or,
                 Seq(initialLoopRunPred,
                     successiveLoopRunPred),
                 Nil,
                 BoolType)
        }
        else {
          DoPrim(Eq, Seq(WRef(stages(i - 1)), one), Nil, BoolType)
        }

        val stageTfStmt =  if (i == loopStages.size) {
          Connect(NoInfo,
                  WRef(stageEnd),
                  Mux(stageTfPred, one, zero, BoolType))
        }
        else {
          Connect(NoInfo,
                  WRef(stages(i)),
                  Mux(stageTfPred, one, zero, BoolType))
        }
        stageTransformBlock = stageTransformBlock ++ Seq(stageTfStmt)
      }

      for (i <- 0 until loopStages.size) yield {
        val stagePred = DoPrim(Eq, Seq(WRef(stages(i)), one),
                               Nil, BoolType)
        var schedStmts = Seq[Statement]()
        // Prioritize memUnits
        for (node <- loopStages(i)) yield {
          if (memUnits.contains(node)) {
            schedStmts = schedStmts ++ Seq(schedUnits(node)._2)
          }
        }
        for (node <- loopStages(i)) yield {
          if (!memUnits.contains(node)) {
            schedStmts = schedStmts ++ Seq(schedUnits(node)._2)
          }
        }
         
        val block = Block(schedStmts)
        val whenStmt = Conditionally(NoInfo, stagePred, block, EmptyStmt)
        fsmBlock = fsmBlock ++ Seq(whenStmt)
      }

      Block(stages ++
            Seq(stageBegin) ++
            Seq(stageEnd) ++
            stageTransformBlock ++
            Seq(nonSchedStmts) ++
            fsmBlock)
    }

    def findLoop(s: Statement): Statement = s match {
      case Loop(info, pred, body) =>
        defUseMap.clear()
        conMap.clear()
        schedUnits.clear()
        conUnits.clear()
        memUnits.clear()
        memWMap.clear()
        dfEdges.clear()
        ordEdges.clear()
        loopStages.clear()

        checkConnect(s)
        buildDepEdges()
        val loopStmts = buildFSM(pred, body)

        println("defUseMap: " + defUseMap)
        println("conMap: " + conMap)
        println("schedUnits: " + schedUnits)
        println("conUnits: " + conUnits)
        println("memUnits: " + memUnits)
        println("memWMap: " + memWMap)
        println("dfEdges: " + dfEdges)
        println("ordEdges: " + ordEdges)
        println("loopStages: " + loopStages)

        loopStmts
      case DefRegister(info, name, tpe, clock, reset, init) =>
        clk = clk ++ Seq(clock)
        rst = rst ++ Seq(reset)
        s map findLoop
      case _ => s map findLoop
    }

    val stmt = findLoop(s)
    stmt
  }

  def execute(state: CircuitState): CircuitState = {
    val c = state.circuit
    val renames = RenameMap()
    renames.setCircuit(c.main)
    val modulesx = c.modules map {
      case m: ExtModule => m
      case m: Module =>
        renames.setModule(m.name)
        Module(m.info, m.name, m.ports, looptransform(renames)(m.body))
    }
    val result = Circuit(c.info, modulesx, c.main)
    CircuitState(result, outputForm, state.annotations, Some(renames))
  }
}
