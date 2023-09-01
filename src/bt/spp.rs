#![allow(non_upper_case_globals)]
#![allow(non_snake_case)]

use core::cmp::min;
use core::convert::TryInto;
use core::ffi;
use core::fmt::{self, Debug};
use core::sync::atomic::{AtomicBool, Ordering};
use core::{borrow::Borrow, marker::PhantomData};

use enumset::{EnumSet, EnumSetType};

use crate::sys::*;

use log::debug;

use num_enum::TryFromPrimitive;

use super::{BdAddr, BtCallback, BtClassicEnabled, BtDriver};
use crate::private::cstr::{from_cstr_ptr, to_cstring_arg};


#[derive(Debug)]
pub enum Role {
  Master,
  Slave,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, TryFromPrimitive)]
#[repr(u32)]
pub enum Mode {
  // When data is coming, a callback will come with data
  Callback,
  // Use VFS to write/read data
  Vfs,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, TryFromPrimitive)]
#[repr(u32)]
pub enum Status {
  /// Successful operation.
  Success,
  /// Generic failure.
  Failure,
  /// Temporarily can not handle this request.
  Busy,
  /// No data
  NoData,
  /// No more resource
  NoResource,
  /// SPP module shall init first
  NeedInit,
  /// SPP module shall deinit first
  NeedDeinit,
  /// Connection may have been closed
  NoConnection,
  /// No SPP server
  NoServer,
}

#[derive(Debug)]
#[repr(u8)]
pub enum SppEvent<'a> {
  Initialized {
    status: Status,
  },
  Deinitialized {
    status: Status,
  },
  DiscoveryComplete {
    status: Status,
    /// channel #
    scn: &'a [u8],
    // service_name
    service_name: &'a str,
  },
  ClientConnectionOpened {
    status: Status,
    /// The connection handle
    handle: u32,
    /// The file descriptor only for ESP_SPP_MODE_VFS
    fd: i32, // TODO: what do we do here?
    /// The peer address
    rem_bda: BdAddr,
  },
  ClientConnectionClosed {
    status: Status,
    // PORT status
    port_status: u32,
    /// The connection handle
    handle: u32,
    /// FALSE, if local initiates disconnect
    is_async: bool,
  },
  ServerStarted {
    status: Status,
    /// The connection handle
    handle: u32,
    sec_id: u8,
    /// Server channel number
    scn: u8,
    /// TRUE to use co_rfc_data
    use_co: bool,
  },
  ClientInitiatedConnection {
    status: Status,
    /// The connection handle
    handle: u32,
    sec_id: u8,
    /// TRUE to use co_rfc_data
    use_co: bool,
  },
  DataReveived {
    status: Status,
    /// The connection handle
    handle: u32,
    /// The data received
    data: &'a [u8],
  },
  CongestionStatus {
    status: Status,
    /// The connection handle
    handle: u32,
    /// TRUE, congested. FALSE, uncongested
    cong: bool,
  },
  WriteCompleted {
    status: Status,
    /// The connection handle
    handle: u32,
    /// The length of the data written.
    len: usize,
    /// congestion status
    cong: bool,
  },
  ServerConnectionOpened {
    status: Status,
    /// The connection handle
    handle: u32,
    /// The new listen handle
    new_listen_handle: u32,
    /// The file descriptor only for ESP_SPP_MODE_VFS
    fd: i32,
    /// The peer address
    rem_bda: BdAddr,
  },
  ServerStopped {
    status: Status,
    /// Server channel number
    scn: u8,
  },
  VfsRegstered {
    status: Status,
  },
  VfsUnregistered {
    status: Status,
  },
}

impl SppEvent<'_> {
  fn discriminant(&self) -> u8 {
    // SAFETY: Because `Self` is marked `repr(u8)`, its layout is a `repr(C)` `union`
    // between `repr(C)` structs, each of which has the `u8` discriminant as its first
    // field, so we can read the discriminant without offsetting the pointer.
    unsafe { *<*const _>::from(self).cast::<u8>() }
  }
}


#[allow(non_upper_case_globals)]
impl<'a> From<(esp_spp_cb_event_t, &'a esp_spp_cb_param_t)> for SppEvent<'a> {
    fn from(value: (esp_spp_cb_event_t, &'a esp_spp_cb_param_t)) -> Self {
        let (event, param) = value;

        unsafe {
            match event {
              esp_spp_cb_event_t_ESP_SPP_INIT_EVT => Self::Initialized {
                status: param.init.status.try_into().unwrap(),
              },
              esp_spp_cb_event_t_ESP_SPP_UNINIT_EVT => Self::Deinitialized {
                status: param.uninit.status.try_into().unwrap(),
              },
              esp_spp_cb_event_t_ESP_SPP_DISCOVERY_COMP_EVT => Self::DiscoveryComplete {
                status: param.disc_comp.status.try_into().unwrap(),
                scn: core::slice::from_raw_parts(
                  param.disc_comp.scn.as_ptr() as *const _,
                  param.disc_comp.scn_num as _
                ),
                service_name: core::str::from_utf8_unchecked(
                  core::slice::from_raw_parts(
                    param.disc_comp.service_name.as_ptr() as *const _,
                    strlen(param.disc_comp.service_name.as_ptr() as *const _) as _
                  )
                ),
              },
              esp_spp_cb_event_t_ESP_SPP_OPEN_EVT => Self::ClientConnectionOpened {
                status: param.open.status.try_into().unwrap(),
                handle: param.open.handle,
                fd: param.open.fd,
                rem_bda: param.open.rem_bda.into(),
              },
              esp_spp_cb_event_t_ESP_SPP_CLOSE_EVT => Self::ClientConnectionClosed {
                status: param.close.status.try_into().unwrap(),
                port_status: param.close.port_status,
                handle: param.close.handle,
                is_async: param.close.async_,
              },
              esp_spp_cb_event_t_ESP_SPP_START_EVT => Self::ServerStarted {
                status: param.start.status.try_into().unwrap(),
                handle: param.start.handle,
                sec_id: param.start.sec_id,
                scn: param.start.scn,
                use_co: param.start.use_co,
              },
              esp_spp_cb_event_t_ESP_SPP_CL_INIT_EVT => Self::ClientInitiatedConnection {
                status: param.cl_init.status.try_into().unwrap(),
                handle: param.cl_init.handle,
                sec_id: param.cl_init.sec_id,
                use_co: param.cl_init.use_co,
              },
              esp_spp_cb_event_t_ESP_SPP_DATA_IND_EVT => Self::DataReveived {
                status: param.data_ind.status.try_into().unwrap(),
                handle: param.data_ind.handle,
                data: core::slice::from_raw_parts(
                  param.data_ind.data,
                  param.data_ind.len as _
                ),
              },
              esp_spp_cb_event_t_ESP_SPP_CONG_EVT => Self::CongestionStatus {
                status: param.cong.status.try_into().unwrap(),
                handle: param.cong.handle,
                cong: param.cong.cong,
              },
              esp_spp_cb_event_t_ESP_SPP_WRITE_EVT => Self::WriteCompleted {
                status: param.write.status.try_into().unwrap(),
                handle: param.write.handle,
                len: param.write.len as _,
                cong: param.write.cong,
              },
              esp_spp_cb_event_t_ESP_SPP_SRV_OPEN_EVT => Self::ServerConnectionOpened {
                status: param.srv_open.status.try_into().unwrap(),
                handle: param.srv_open.handle,
                new_listen_handle: param.srv_open.new_listen_handle,
                fd: param.srv_open.fd,
                rem_bda: param.srv_open.rem_bda.into(),
              },
              esp_spp_cb_event_t_ESP_SPP_SRV_STOP_EVT => Self::ServerStopped {
                status: param.srv_stop.status.try_into().unwrap(),
                scn: param.srv_stop.scn,
              },
              esp_spp_cb_event_t_ESP_SPP_VFS_REGISTER_EVT => Self::VfsRegstered {
                status: param.vfs_register.status.try_into().unwrap(),
              },
              esp_spp_cb_event_t_ESP_SPP_VFS_UNREGISTER_EVT => Self::VfsUnregistered {
                status: param.vfs_unregister.status.try_into().unwrap(),
              },
              _ => todo!(),
            }
          }
        }
      }

pub struct EspSpp<'d, M, T>
where
    M: BtClassicEnabled,
    T: Borrow<BtDriver<'d, M>>,
{
    _driver: T,
    initialized: AtomicBool,
    _p: PhantomData<&'d ()>,
    _m: PhantomData<M>,
}


impl<'d, M, T> EspSpp<'d, M, T>
where
    M: BtClassicEnabled,
    T: Borrow<BtDriver<'d, M>>,
{
    pub fn new(driver: T) -> Result<Self, EspError> {
      Ok(Self {
          _driver: driver,
          initialized: AtomicBool::new(false),
          _p: PhantomData,
          _m: PhantomData,
      })
    }

    pub fn initialize<F>(&self, events_cb: F) -> Result<(), EspError>
    where
        F: Fn(SppEvent) + Send + 'd
    {
      CALLBACK.set(events_cb)?;
      esp!(unsafe { esp_spp_register_callback(Some(Self::event_handler)) })?;
      self.initialized.store(true, Ordering::SeqCst);
      Ok(())
    }

    pub fn init(&self, mode: Mode) -> Result<(), EspError> {
        esp!(unsafe { esp_spp_init(mode as _) })
    }

    pub fn enhanced_init(&self, cfg: &esp_spp_cfg_t) -> Result<(), EspError> {
        esp!(unsafe { esp_spp_enhanced_init(cfg as *const _) })
    }

    pub fn deinit(&self) -> Result<(), EspError> {
      esp!(unsafe { esp_spp_deinit() })
    }

    pub fn start_discovery(&self, bd_addr: &BdAddr) -> Result<(), EspError> {
        esp!(unsafe { esp_spp_start_discovery(bd_addr as *const _ as *mut _) })
    }

    pub fn connect(&self, sec_mask: esp_spp_sec_t, role: Role, remote_scn: u8, bd_addr: &esp_bd_addr_t) -> Result<(), EspError> {
      esp!(unsafe { esp_spp_connect(sec_mask, role as _, remote_scn, bd_addr as *const _ as *mut _) })
    }

    pub fn disconnect(&self, handle: u32) -> Result<(), EspError> {
        esp!(unsafe { esp_spp_disconnect(handle) })
    }

    pub fn start_srv(&self, sec_mask: esp_spp_sec_t, role: Role, local_scn: u8, name: &str) -> Result<(), EspError> {
      let n = to_cstring_arg(name)?;
      esp!(unsafe { esp_spp_start_srv(sec_mask, role as _, local_scn, n.as_ptr())})
    }

    pub fn stop_srv(&self) -> Result<(), EspError> {
      esp!(unsafe { esp_spp_stop_srv()})
    }

    pub fn stop_srv_scn(&self, scn: u8)-> Result<(), EspError> {
      esp!(unsafe { esp_spp_stop_srv_scn(scn)})
    }


    pub fn write(&self, handle: u32, data: &[u8]) -> Result<(), EspError> {
      esp!(unsafe { esp_spp_write(handle, data.len() as _, data.as_ptr() as *const _ as *mut _)})
    }


    pub fn vfs_register(&self) -> Result<(), EspError> {
      esp!(unsafe { esp_spp_vfs_register()})
    }


    pub fn vfs_unregister(&self) -> Result<(), EspError> {
      esp!(unsafe { esp_spp_vfs_unregister()})
    }

    unsafe extern "C" fn event_handler(
      event: esp_spp_cb_event_t,
      param: *mut esp_spp_cb_param_t,
    ) {
        if let Some(param) = unsafe { param.as_ref() } {
            let event = SppEvent::from((event, param));

            debug!("Got event {{ {:#?} }}", event);

            CALLBACK.call(event);
        }
    }
}

impl<'d, M, T> Drop for EspSpp<'d, M, T>
where
    M: BtClassicEnabled,
    T: Borrow<BtDriver<'d, M>>,
{
    fn drop(&mut self) {
      if self.initialized.load(Ordering::SeqCst) {
        CALLBACK.clear().unwrap();
      }
    }
}

static CALLBACK: BtCallback<SppEvent, ()> = BtCallback::new(());
