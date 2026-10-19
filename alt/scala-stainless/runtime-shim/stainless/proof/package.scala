package stainless

package object proof {
  def check(prop: Boolean): Unit = {
    require(prop)
    ()
  }
}
