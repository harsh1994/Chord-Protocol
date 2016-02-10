/**
 * @author harsh
 */

import scala.math._
import scala.concurrent._
import ExecutionContext.Implicits.global
import scala.util.Random
import akka.actor._
import scala.concurrent.duration._
import scala.collection.mutable.ArrayBuffer
import scala.concurrent.ExecutionContext.Implicits.global
import scala.collection.mutable.ListBuffer
import java.security.NoSuchAlgorithmException
import java.security.MessageDigest
import scala.concurrent.Future
import scala.util.{Failure, Success}
import scala.util.Random
import akka.pattern.ask


case object START
case object LOOKUP
case object PRINTFINGER
case object PRINTFINGERTABLE
case class EXIT(hop:Int)
case class JOIN(first:Boolean,idref:ActorRef,arbref:ActorRef,pred:ActorRef,succ:ActorRef)
case class FIND_SUCC()
case class FIND_PRED()
case class FINGER()
case class INIT_FINGER()
case class CLOSEST_PREC_FINGER()
case class UPDATE_OTHERS()
case class UPDATE_FINGER()
case class SETPRED(successor:ActorRef,idref1:ActorRef)
case class SETPREDECESSOR(id:ActorRef)
case class SETFINGER(p:Int,i:Int,j:Int)
case class UPDATEFINGER(i:Int,j:Int)
case class LOOKUP(key:Int,hop:Int)
case class LOOKNEXT(key:Int,node:Int,hop:Int)

object SHA{

	def sha1Hash(text: String) : String =
		{
			return java.security.MessageDigest.getInstance("SHA-1").digest(text.getBytes()).map(0xFF & _).map { "%02x".format(_) }.foldLeft(""){_ + _}
		}
}


class ActorCall(val numnodes:Int, val numrequests:Int, m:Int, id : Int, arb:Int) extends Actor
{

	var idref1,arbref1:ActorRef = null
			var predecessor,successor, n_dash:ActorRef = null
			var ndash_id:Double = 0
			var arb_pred,arb_succ:ActorRef = null
			var start_arb,node_arb = new Array[Int](m+1)
			var start, begin, end, node = new Array[Int](m+1)
      var hop1,node_lookup = 0

			def receive =
		{

		case JOIN(first,idref,arbref,pred,succ) =>{
			idref1 = idref
					arbref1 = arbref
					predecessor = pred
					successor = succ

					if(first)
					{
						normal_call()
					}
					else
					{
						first_call()
					}
		}
		case SETPREDECESSOR(idref)=>{
			predecessor = idref
		}
		case UPDATEFINGER(i,j)=>{
			node(j) = i
		}

		case LOOKUP(key,hop)=>{
			hop1 = hop + 1
      if(key == id)
      {
      sender ! EXIT(hop1)
      }
      else{
					for(i <-0 to m-1){
						if(i < m-1){
							if(key >= start(i) && key < start(i+1)){
								hop1 = hop1 + 1
                sender ! EXIT(hop1)
							}
						}
            else
            {
              node_lookup = node(m-1)
              sender ! LOOKNEXT(key,node_lookup,hop1)
            }
					}
      }
		}

		}
	//
	//
	def first_call()
	{
		for (i <- 0 to m-1)
		{
			start(i) = id
					begin(i) = id
					node(i) = id
		}
		predecessor = idref1
	}

	def normal_call()
	{
		initialize()
		init_finger_table(arb)
		update_others()
	}

	def initialize()
	{
		for(i <- 0 to m-1){
			start(i) = id + (pow(2,i) % pow(2,m)).toInt
					begin(i) = start(i)
		}
	}
	def init_finger_table(id1:Int)
	{
		val future2 = ask (arbref1, getnode)(500)
				future2 onSuccess{
				case ans:Array[Int] => {
					node_arb = ans
				}
		}
		val future1 = ask (successor, predecessor)(500)
				future1 onSuccess{
				case ans:ActorRef => {
					arb_pred = ans
				}
		}

		node(0) = node_arb(0)
				predecessor = arb_pred
				sender ! SETPRED(successor,idref1)

				for(i <- 0 to m-1)
				{
					if(start(i+1) > id && start(i+1) < node(i))
					{
						node(i+1) = node(i)
					}
					else{
						node(i+1) = node_arb(i+1)
					}
				}
	}

	def update_others()
	{
		Thread.sleep(500)
		for(i <- 0 to m-1)
		{
			var p = find_predecessor(id - pow(2,i))
					update_finger_table(p,id,i)
		}
	}

	def update_finger_table(p:Int,s:Int,i:Int)
	{
		var nodes = new Array[Int](m+1)
				var id_p = 0
				if(s >= p && s < node(i))
				{
					nodes(i) = s
							sender ! SETFINGER(p,nodes(i),i)
							var p1 = predecessor

							val future1 = ask (p1,id)(500)
							future1 onSuccess{
							case ans:Int => {
								id_p = ans
							}
					}

					update_finger_table(id_p,s,i)
				}
	}

	def find_successor(id1 : Double) : Int =
		{
			ndash_id = find_predecessor(id1)
					var n = ndash_id.toInt
					return node(start(n))
		}

	def find_predecessor(id1 : Double) : Int =
		{
			ndash_id = id
					var n = ndash_id.toInt
					while(id1 < n || id1 >= node(start(n)))
					{
						n = closest_preceding_finger(n)
					}
			return n
		}

	def closest_preceding_finger(id1 : Int) : Int =
		{
			for(i <- (m-1) to 0)
			{
				if(node(i) > id && node(i) < id1)
				{
					return node(i)
				}
			}
			return id
		}

	def getstart():Array[Int] =
		{
			return start
		}

	def getnode():Array[Int] =
		{
			return node
		}

	def getpred():ActorRef =
		{
			return predecessor
		}
}




class Master(val numnodes:Int, val numrequests:Int) extends Actor
{
    	var m = 8
			var id,no = numnodes
      var counter = 0
			var node_array,id_array = new ArrayBuffer[ActorRef]()
			var id_arr,node_arr,key_arr = new ArrayBuffer[Int]()
			var actor = new ArrayBuffer[ActorRef]()
			var byte = Array[Byte]()

			var ip : String = "192.168.1.139"
			var pred = 0
			var count = 0
			var j:String = null

			var first = false

			def receive = {
			case START =>{

				for(i <- 1025 to (1025+127))
				{
					count = count+1
							j = Integer.toString(i)
							j = ip.concat(j)
							var hash = SHA.sha1Hash(j)
							byte = hash.getBytes()
							var s_byte = new String(byte).toString().substring(0,m/2)
							//              println("sbyte "+s_byte)
							id = Integer.parseInt(s_byte,16)
							var arb : Int = 0

							if(i == 1025)
							{
								arb = id
							}

							id_arr += id
									//                println("id "+id)

									if(count <= numnodes){                                                                //Id is of a node
										node_arr += id
												//                  println(node_arr(i-1025))
												actor += context.actorOf(Props(new ActorCall (numnodes, numrequests, m, id, arb)), name = "actor" + id)
												//                        println(actor(i-1025))
												id_array += actor(i-1025)
												node_array += actor(i-1025)

                        if(count>1145 && count<1152)
                          key_arr += id

									}
									else                                                                                  // Id is of a key
									{
										key_arr += id
									}
				}
				//				scala.util.Sorting.stableSort(node_array)

				for(i <- 0 to node_array.length-1)
				{
					if(i==0){
						actor(i) ! JOIN(first, id_array(i), node_array(0), node_array(node_array.length-1), node_array(i+1))
						first = true
						Thread.sleep(500)

					}
					else if(i == node_array.length-1)
					{
						actor(i) ! JOIN(first,id_array(i),node_array(0),node_array(i-1),node_array(0))
						first = true
						Thread.sleep(500)

					}
					else
					{
						actor(i) ! JOIN(first,id_array(i),node_array(0),node_array(i-1),node_array(i+1))
						first = true
						Thread.sleep(500)
					}
				}
        Thread.sleep(1000)
        for(i <- 0 to numrequests-1)
        {
        self ! LOOKUP
        }


			}
			//    println("Id_array"+id_array(i))
			//    id = id.substring(0,1025)

			case SETPRED(successor,idref)=>{
				successor ! SETPREDECESSOR(idref)
			}
			case SETFINGER(p,i,j)=>{
				var act = findActor(p)
        node_array(act) ! UPDATEFINGER(i,j)
			}
			case PRINTFINGER=>{

				sender ! PRINTFINGERTABLE

			}

      case LOOKUP =>{
        var key_look = Random.nextInt(key_arr.length-1)
        var node_look = Random.nextInt(node_arr.length-1)
        actor(node_look) ! LOOKUP(key_arr(key_look),0)

      }

      case LOOKNEXT(key:Int,node:Int,hop:Int) =>{
        counter = counter + 1
        var set = findActor(node)
        node_array(set) ! LOOKUP(key,hop+1)

        if(counter == numrequests * 2)
        {
          var avg = (hop + 1) / numrequests
          self ! EXIT(avg)
        }
      }
      case EXIT(hop:Int) =>
        {
        println("Average number of hops="+hop)
        System.exit(0)
        }
			}

      def findActor(id:Int):Int =
      {
        var n = 0
        for(i <- 0 to node_arr.length-1)
            {
              if(node_arr(i)==id)
              {
                n = i
              }
            }
        return n
      }
}

object project3{
	def main(args: Array[String]){
		var numnodes = args(0).toInt
				var numrequests = args(1).toInt

				val system = ActorSystem("ChordProtocol")
				val master = system.actorOf(Props(new Master (numnodes, numrequests)),name="master")
				master ! START

	}
}
