all: 
	./run.sh
.PHONY: cleanlsp
cleanlsp: 
	((pkill -f java || true) && (echo $(pgrep haskell-language*) | xargs kill -9 || true)) || true