all:
# 	stainless --no-colors=true src/RightBiasing.scala > results.txt || true
	stainless --no-colors=true src/ListUtils.scala src/RightBiasing.scala > results.txt || true
list: 
	stainless --no-colors=true src/ListUtils.scala src/RightBiasing.scala > results.txt || true
.PHONY: cleanlsp
cleanlsp: 
	((pkill -f java || true) && (echo $(pgrep haskell-language*) | xargs kill -9 || true)) || true