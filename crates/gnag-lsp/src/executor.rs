use std::{
    any::Any,
    cell::Cell,
    sync::{atomic::AtomicI32, mpsc, Arc},
    thread::JoinHandle,
};

use lsp::msg::Message;

pub struct TaskContext<'a> {
    // this field must only be read!
    current_file_version: &'a AtomicI32,
    task_start_file_version: i32,
    sender: &'a mpsc::Sender<Message>,
}

struct TaskCancelledPanic;

impl<'a> TaskContext<'a> {
    pub fn check_valid(&self) {
        let current = self
            .current_file_version
            .load(std::sync::atomic::Ordering::Relaxed);

        if current != self.task_start_file_version {
            std::panic::panic_any(TaskCancelledPanic);
        }
    }
}

pub struct Task {
    fun: Box<dyn FnOnce(TaskContext<'_>) + Send>,
    file_version: i32,
}

pub struct Executor {
    cached_file_version: Cell<i32>,
    // you may write to this atomic variable only by calling `update_file_version()`
    current_file_version: Arc<AtomicI32>,
    task_sender: mpsc::Sender<Task>,
    thread: JoinHandle<()>,
}

impl Executor {
    pub fn new(sender: mpsc::Sender<Message>) -> Executor {
        todo!()
    }
    pub fn launch(
        &self,
        fun: impl FnOnce(TaskContext<'_>) + Send + 'static,
    ) -> Result<(), mpsc::SendError<Task>> {
        self.task_sender.send(Task {
            fun: Box::new(fun),
            file_version: self.cached_file_version.get(),
        })
    }
    pub fn update_file_version(&self, new_version: i32) {
        let diff = new_version.wrapping_sub(self.cached_file_version.get());
        if diff != 1 {
            log::error!("Version must increase by one each time!");
        }
        self.cached_file_version.set(new_version);
        self.current_file_version
            .store(new_version, std::sync::atomic::Ordering::Relaxed);
    }
}

fn executor_loop(sender: mpsc::Sender<Message>, receiver: mpsc::Receiver<Task>) {
    loop {
        let panic: Result<(), Box<dyn Any + Send>> =
            std::panic::catch_unwind(|| match receiver.recv() {
                Ok(_) => todo!(),
                Err(_) => todo!(),
            });

        if let Err(err) = panic {
            if err.is::<TaskCancelledPanic>() {
                continue;
            } else {
                std::panic::resume_unwind(err);
            }
        }
    }
}
