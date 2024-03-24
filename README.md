# BSan 
Bsan is a hybrid detection combining offline analysis and online detection tool. 

The offline analysis is based on Dyninst, a binary analysis tool. BSan uses Dyninst to analyze the binary to get the needed information, such as instruction operands, opcode, etc. Based on the data, our offline analysis can identify unnecessary detection, propagation, and instrumentation to reduce the performance overhead of BSan

The online detection is build from DynamoRio, a dynamic binary instrumentation tool. Our tool retrieves the data from offline analysis and Dynamorio, will instrument the binary, and record the allocated heap objects or stack frames. If there is an action that violates our recorded data, an according alarm will be raised.

The testing cases will be uploaded soon. Thanks!
