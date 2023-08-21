# test_tipc
  create a simple tipc case according to Fproof framework

## framework

  you must install docker first, and pull the environment by 'docker pull mancanfly53373931/docker_hv6:hv6'.
  run the docker image and put test_tipc code folder under a path.

  like this:

  'docker run -it -v /root/project:/opt tipc_image /bin/bash'

  /root/project ： Local directory to be mounted
  /opt: You can see the files or directories you have mounted in that directory
  tipc_image：Image name, using the number of the image should also work
  /bin/bash: create a new bash
  

## how to run

  test the chan_init interface at the same environment

To compile:
    must run compile first, it includes compile .c --> .ll , then compose any .ll --> TIPC.ll, at end, translating
    TIPC.ll --> TIPC.py.
    
    `make`
     
To run verfiy:(must complie first)
    running testcase in main.py. it verifies a test case 'chan_init'. it verifies the equals  
    between statemachine and lowwer code(behavior as contex object in python).
    
    `make verify`
      
To run app
 
    `make app`
      
## file structure
    
- TEST_TIPC
  - TIPC.c       // source code
  - invariant.py    // as you see
  - main.py         // test case
  - specs.py        // specification of three funcation
  - irpy            // a tool translate llvm ir to python for symbolic execution.
  
- x86_64            // build dir

- script            // clear undefined behavior in llvm ir.

- datatype          // define our state machine.

- libirpy           // as the name defined.
