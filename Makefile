compiler:
	$(shell which cargo) build

.PHONY: clean
clean: 
	rm -rf target

