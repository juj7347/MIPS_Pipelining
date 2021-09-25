# MIPS_Pipelining

MIPS 프로세서에 해저드 컨트롤을 포함한 파이프라이닝 기능을 구현하였습니다

## 구현방식

사용언어: Verilog HDL
1. MIPS는 기본적으로 Single Cycle 프로세서이기 때문에 한 클럭 사이클에 한 Instruction을 처리합니다. 따라서 프로젝트의 주제인 파이프라이닝을 구현하기 위해 5단계의 Intrsuction 처리 Cycle의 각 단계마다 플립플랍 모듈을 추가해 한 클럭 사이클당 한 단계씩만 진행하도록 하였습니다.
2. 각 클럭 사이클마다 하나의 Instruction을 받으므로 이전 Instruction이 한 단계 진행되었을 때 다음 Instruction을 받게 됩니다.
3. 해저드 컨트롤을 통한 레지스터 값 forwarding, stall, flush등을 통해 파이프라이닝시 발생할 수 있는 해저드를 처리하였습니다.