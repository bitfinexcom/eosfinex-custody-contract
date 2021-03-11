ifeq ($(USE_CHAIN_ID_FOR_TESTS),yes)
  FLAGS=-DUSE_CHAIN_ID_FOR_TESTS
else
  FLAGS=
endif
eosfinex.wasm : eosfinex.cpp
	eosio-cpp $(FLAGS) eosfinex.cpp
