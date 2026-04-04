// KernelMachine trait implementation for ProtocolMachine.
impl KernelMachine for ProtocolMachine {
    fn kernel_step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, ProtocolMachineError> {
        ProtocolMachine::kernel_step_round(self, handler, n)
    }
}
