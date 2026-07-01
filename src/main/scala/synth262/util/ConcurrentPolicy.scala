package synth262.util

enum ConcurrentPolicy:
  case Single
  case Fixed(nThread: Int)
  case Auto
