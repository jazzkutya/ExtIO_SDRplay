/*
This is free and unencumbered software released into the public domain.

Anyone is free to copy, modify, publish, use, compile, sell, or
distribute this software, either in source code form or as a compiled
binary, for any purpose, commercial or non-commercial, and by any
means.

In jurisdictions that recognize copyright laws, the author or authors
of this software dedicate any and all copyright interest in the
software to the public domain. We make this dedication for the benefit
of the public at large and to the detriment of our heirs and
successors. We intend this dedication to be an overt act of
relinquishment in perpetuity of all present and future rights to this
software under copyright law.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR
OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
OTHER DEALINGS IN THE SOFTWARE.

For more information, please refer to <http://unlicense.org>
*/


// some compatibility hacks that should be in a separate header file
typedef void* HWND;
typedef unsigned int UINT;
typedef UINT* UINT_PTR;

// MessageBox uType stuff
#define MB_ICONERROR 1
#define MB_OK 2
#define MB_SYSTEMMODAL 4
#define MB_TOPMOST 8
#define MB_ICONEXCLAMATION 16

#define TEXT(arg) arg
#define Sleep(msec) usleep((msec)*1000)
#define __stdcall

#define FALSE 0
#define TRUE 1

#define sprintf_s snprintf

// --------------------------------------------------------

#include <new>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <vector>
#include "ExtIO_SDRplay.h"
#include <mirsdrapi-rsp.h>
#include <sys/types.h>
#include <sys/timeb.h>
#include <ctime>
#include <unistd.h>

using namespace std;

#define EXTIO_HWTYPE_16B 3

#define ONE_OVER_32768 (0.000030517578125f)
#define	ALWAYS_FULL_TUNE 0
#define	COPY_SAMPLEDATA_TO_AGC_BUFFERS	0
#define IDC_BUFFER 200
#define IDC_Decimation 201
#define ID_AGCUPDATE 202
#define LO120MHz 24576000
#define LO144MHz 22000000
#define LO168MHz 19200000
#define DCCompensationTime 75
#define STATIC 0
#define PERIODIC1 1
#define PERIODIC2 2
#define PERIODIC3 3
#define ONESHOT 4
#define CONTINUOUS 5
#define DCTrackTimeInterval 2.93
#define DEBUG 0
#define DcRemovalFilterCoef (short)0.002

#define TCHAR char

//Globals for monioring SDRplay Condition.
static int DcCompensationMode;
static int TrackingPeriod;
static int RefreshPeriodMemory;
static bool PostTunerDcCompensation;
double TrackTime;
static double Frequency = 98.8;			// nominal / desired frequency
int LowerFqLimit;
int IFmodeIdx = 0;
int FqOffsetPPM = 0;
volatile int GainReduction = 60;		// variables accessed from different threads should be volatile!
mir_sdr_If_kHzT IFMode = mir_sdr_IF_Zero;
mir_sdr_Bw_MHzT Bandwidth = mir_sdr_BW_1_536;
volatile int BandwidthIdx = 3;
int DecimationIdx = 0;
int LNAGRTHRES = 59;
int AGCsetpoint = -15;
bool AGCEnabled = true;
int down_conversion_enabled = 1;
int LOplan = LO120MHz;
bool LOplanAuto = true;
bool LOChangeNeeded = FALSE;
TCHAR msgbuf[255];
static int LastGrToggle = -1;
clock_t StartTime, CurrentTime;
int ExecutionTime;
static double lastFreq = -1.0;
static int lastFreqBand = -1;
static int lastLNAGRTHRES = -1;
static int lastGainReduction = -1;
bool invertSpectrum = false;
double FreqOffsetInvSpec = 0.0;
int SampleCount = 0;				// number of I/Q frames
volatile bool DecimationEN = false;

//Other Globals
static int buffer_len_samples;		// number of samples in one buffer (= 2 * number of I/Q frames)
HWND ghwndDlg = 0;
UINT_PTR m_timer = 0;
volatile int ThreadExitFlag = 0;
bool Initiated = FALSE;
bool Running = FALSE;
static int ppm_default=0;
int SampleRateIdx = 0;
int SampleRateDisplayIdx = 0;

typedef struct SR
{
	double DisplayValue;		//Values to display in DialogBox	
	double SampleRate;			//Sample Rate to be programmed to SDRplay 
	int DownSample;				//Required Downsample ratio to achieve some Sample Rates
} SR_;

struct SR SampleRate[] = {
						 { 0.2,  2.0,   9 }, 
						 { 0.3,  2.0,   6 }, 
						 { 0.4,  3.0,   7 }, 
						 { 0.5,  2.0,   4 },
						 { 0.6,  4.0,   7 }, 
						 { 0.75, 3.0,   4 },
						 { 0.8,  7.0,   8 }, 
						 { 1.0,  2.0,   2 },		
						 { 2.0,  2.0,   0 }, 
						 { 3.0,  3.0,   0 }, 
						 { 4.0,  4.0,   0 }, 
						 { 5.0,  5.0,   0 }, 
						 { 6.0,  6.0,   0 }, 
						 { 7.0,  7.0,   0 }, 
						 { 8.0,  8.0,   0 }, 
						 { 8.2,  8.192, 0 }
						 };

struct bw_t {
	mir_sdr_Bw_MHzT bwType;
	double			BW;
};

struct ThreadContainer 
{
	int SRConverstionFactor;
	double SampleRate;
	mir_sdr_If_kHzT IFMode;
	mir_sdr_Bw_MHzT Bandwidth;
	int RfToggle;
	int GrToggle;
	bool DcOffsetComp;
};

struct ThreadContainer ThreadVariables;

static bw_t bandwidths[] = {
	{ mir_sdr_BW_0_200, 0.2 },		{ mir_sdr_BW_0_300, 0.3 },		{ mir_sdr_BW_0_600, 0.6 },
	{ mir_sdr_BW_1_536, 1.536 },	{ mir_sdr_BW_5_000, 5.000 },	{ mir_sdr_BW_6_000, 6.000 },
	{ mir_sdr_BW_7_000, 7.000 },	{ mir_sdr_BW_8_000, 8.000 }
};

#define NUM_BANDS	8            //  0				1			2			3			4			5	        6			7       
const double band_fmin[NUM_BANDS] = { 0.1,			12.0, 		30.0,		60.0,		120.0,		250.0,		420.0,		1000.0	};
const double band_fmax[NUM_BANDS] = { 11.999999,	29.999999,  59.999999,	119.999999,	249.999999,	419.999999,	999.999999, 2000.0	};
const int band_LNAgain[NUM_BANDS] = { 24,			24,			24,			24,			24,			24,			7,			5		};	
const int band_MIXgain[NUM_BANDS] = { 19,			19,			19,			19,			19,			19,			19,			19		};	 
const int band_fullTune[NUM_BANDS]= { 1,			1,			1,			1,			1,			1,			1,			1		};
const int band_MaxGR[NUM_BANDS] =	{ 102,			102,		102,		102,		102,		102,		85,			85		};

//static HMODULE ApiDll = NULL;
//HMODULE Dll = NULL;

mir_sdr_Init_t                   mir_sdr_Init_fn = NULL;
mir_sdr_Uninit_t                 mir_sdr_Uninit_fn = NULL;
mir_sdr_ReadPacket_t             mir_sdr_ReadPacket_fn = NULL;
mir_sdr_SetRf_t                  mir_sdr_SetRf_fn = NULL;
mir_sdr_SetFs_t                  mir_sdr_SetFs_fn = NULL;
mir_sdr_SetGr_t                  mir_sdr_SetGr_fn = NULL;
mir_sdr_SetGrParams_t            mir_sdr_SetGrParams_fn = NULL;
mir_sdr_SetDcMode_t              mir_sdr_SetDcMode_fn = NULL;
mir_sdr_SetDcTrackTime_t         mir_sdr_SetDcTrackTime_fn = NULL;
mir_sdr_SetSyncUpdateSampleNum_t mir_sdr_SetSyncUpdateSampleNum_fn = NULL;
mir_sdr_SetSyncUpdatePeriod_t    mir_sdr_SetSyncUpdatePeriod_fn = NULL;
mir_sdr_ApiVersion_t             mir_sdr_ApiVersion_fn = NULL;
mir_sdr_ResetUpdateFlags_t		 mir_sdr_ResetUpdateFlags_fn = NULL;
mir_sdr_DownConvert_t            mir_sdr_DownConvert_fn = NULL;
mir_sdr_SetParam_t			     mir_sdr_SetParam_fn = NULL;

static int buffer_sizes[] = { //in kBytes
	1,		2,		4,		8,
	16,		32,		64,		128,
	256,	512,	1024
};

static int buffer_default=6;// 64kBytes

typedef struct
	{
	char vendor[256], product[256], serial[256];
	} device;

static device *connected_devices = NULL;
static int device_count = 0;

// Thread handle
//HANDLE worker_handle=INVALID_HANDLE_VALUE;
void ThreadProc(ThreadContainer*);
int Start_Thread();
int Stop_Thread();
int FindSampleRateIdx(double);
void SDRplayInitalise(void);
void SaveSettings(void);
void LoadSettings(void);
bool InitRequired(bool, bool, int*, bool*, double, double, mir_sdr_Bw_MHzT, mir_sdr_If_kHzT, int);

/* ExtIO Callback */
void (* WinradCallBack)(int, int, float, void *) = NULL;
#define WINRAD_SRCHANGE 100
#define WINRAD_LOCHANGE 101
#define WINRAD_ATTCHANGE 125
#define HDSDR_RX_IQ		134
#define WINRAD_LOBLOCKED 102
#define WINRAD_LORELEASED 103
#define HDSDR_RX_LEFT	131

//static INT_PTR CALLBACK MainDlgProc(HWND, UINT, WPARAM, LPARAM);
//HWND h_dialog=NULL;

//static INT_PTR CALLBACK AdvancedDlgProc(HWND, UINT, WPARAM, LPARAM);
//HWND h_AdvancedDialog = NULL;

int pll_locked=0;

const char * getMirErrText(mir_sdr_ErrT err)
{
	switch (err)
	{
	case mir_sdr_Success:				return 0;
	case mir_sdr_Fail:					return "Fail";
	case mir_sdr_InvalidParam:			return "Invalid Parameters";
	case mir_sdr_OutOfRange:			return "Out of Range";
	case mir_sdr_GainUpdateError:		return "Gain Update Error";
	case mir_sdr_RfUpdateError:			return "Rf Update Error";
	case mir_sdr_FsUpdateError:			return "Fs Update Error";
	case mir_sdr_HwError:				return "Hw Error";
	case mir_sdr_AliasingError:			return "Aliasing Error";
	case mir_sdr_AlreadyInitialised:	return "Already Initialized";
	case mir_sdr_NotInitialised:		return "Not Initialized";
	default:							return "Unknown";
	}
}


int MessageBox(HWND, const char *msg, const char *title, UINT ignored) {
    fprintf(stderr,"msgbox: %s: %s",title,msg);
}
extern "C"
bool  LIBSDRplay_API __stdcall InitHW(const char *name, const char *model, int& type)
{
	//Following code loads the API into memmory

	//char APIkeyValue[8192];
	//char ToolskeyValue[8192];
	//char tmpStringA[8192];
	//char str[1024 + 8192];
	//DWORD APIkeyValue_length = 8192;
	//DWORD ToolskeyValue_length = 8192;
	//HKEY APIkey;
	mir_sdr_ErrT err;
	mir_sdr_If_kHzT IFMode;
	mir_sdr_Bw_MHzT Bandwidth;
	int error;

    /*
	mir_sdr_Init_fn = (mir_sdr_Init_t)GetProcAddress(ApiDll, "mir_sdr_Init");
	mir_sdr_Uninit_fn = (mir_sdr_Uninit_t)GetProcAddress(ApiDll, "mir_sdr_Uninit");
	mir_sdr_ReadPacket_fn = (mir_sdr_ReadPacket_t)GetProcAddress(ApiDll, "mir_sdr_ReadPacket");
	mir_sdr_SetRf_fn = (mir_sdr_SetRf_t)GetProcAddress(ApiDll, "mir_sdr_SetRf");
	mir_sdr_SetFs_fn = (mir_sdr_SetFs_t)GetProcAddress(ApiDll, "mir_sdr_SetFs");
	mir_sdr_SetGr_fn = (mir_sdr_SetGr_t)GetProcAddress(ApiDll, "mir_sdr_SetGr");
	mir_sdr_SetGrParams_fn = (mir_sdr_SetGrParams_t)GetProcAddress(ApiDll, "mir_sdr_SetGrParams");
	mir_sdr_SetDcMode_fn = (mir_sdr_SetDcMode_t)GetProcAddress(ApiDll, "mir_sdr_SetDcMode");
	mir_sdr_SetDcTrackTime_fn = (mir_sdr_SetDcTrackTime_t)GetProcAddress(ApiDll, "mir_sdr_SetDcTrackTime");
	mir_sdr_SetSyncUpdateSampleNum_fn = (mir_sdr_SetSyncUpdateSampleNum_t)GetProcAddress(ApiDll, "mir_sdr_SetSyncUpdateSampleNum");
	mir_sdr_SetSyncUpdatePeriod_fn = (mir_sdr_SetSyncUpdatePeriod_t)GetProcAddress(ApiDll, "mir_sdr_SetSyncUpdatePeriod");
	mir_sdr_ApiVersion_fn = (mir_sdr_ApiVersion_t)GetProcAddress(ApiDll, "mir_sdr_ApiVersion");
	mir_sdr_ResetUpdateFlags_fn = (mir_sdr_ResetUpdateFlags_t)GetProcAddress(ApiDll, "mir_sdr_ResetUpdateFlags");
	mir_sdr_DownConvert_fn = (mir_sdr_DownConvert_t)GetProcAddress(ApiDll, "mir_sdr_DownConvert");
	mir_sdr_SetParam_fn = (mir_sdr_SetParam_t)GetProcAddress(ApiDll, "mir_sdr_SetParam");
    */
	mir_sdr_Init_fn = mir_sdr_Init;
	mir_sdr_Uninit_fn = mir_sdr_Uninit;
	mir_sdr_ReadPacket_fn = mir_sdr_ReadPacket;
	mir_sdr_SetRf_fn = mir_sdr_SetRf;
	mir_sdr_SetFs_fn = mir_sdr_SetFs;
	mir_sdr_SetGr_fn = mir_sdr_SetGr;
	mir_sdr_SetGrParams_fn = mir_sdr_SetGrParams;
	mir_sdr_SetDcMode_fn = mir_sdr_SetDcMode;
	mir_sdr_SetDcTrackTime_fn = mir_sdr_SetDcTrackTime;
	mir_sdr_SetSyncUpdateSampleNum_fn = mir_sdr_SetSyncUpdateSampleNum;
	mir_sdr_SetSyncUpdatePeriod_fn = mir_sdr_SetSyncUpdatePeriod;
	mir_sdr_ApiVersion_fn = mir_sdr_ApiVersion;
	mir_sdr_ResetUpdateFlags_fn = mir_sdr_ResetUpdateFlags;
	mir_sdr_DownConvert_fn = mir_sdr_DownConvert;
	mir_sdr_SetParam_fn = mir_sdr_SetParam;

	// The code below performs an init to check for the presence of the hardware. An uninit is done afterwards.

	IFMode = mir_sdr_IF_Zero;
	Bandwidth = mir_sdr_BW_1_536;
	lastFreqBand = -1;

	err = mir_sdr_Init_fn(60, 2.0, 98.8, Bandwidth, IFMode, &SampleCount);
	if (err == mir_sdr_Success)
	{
		name = "SDRplay";
		model = "Radio Spectrum Processor";
		type = 3;	
		mir_sdr_Uninit_fn();
		return TRUE;
	}
	else
	{
		MessageBox(NULL, TEXT("Error: SDRplay Hardware not found"), TEXT("SDRplay ExtIO DLL"), MB_ICONERROR | MB_OK);
		return TRUE;
	}
	return TRUE;
}

extern "C"
bool  LIBSDRplay_API __stdcall OpenHW()
{
    //h_dialog=CreateDialog(hInst, MAKEINTRESOURCE(IDD_SDRPLAY_SETTINGS), NULL, (DLGPROC)MainDlgProc);
	//ShowWindow(h_dialog, SW_HIDE);
	return TRUE;
}

extern "C"
long LIBSDRplay_API __stdcall SetHWLO(unsigned long freq)
{
	int FreqBand = 0;
	int LNAMIN = 0;
	int MAXGR = 0;

	WinradCallBack(-1, WINRAD_LOBLOCKED, 0, NULL);
	if (freq > (unsigned long)2000000000)
	{
		MessageBox(NULL, "Warning Out of Range", TEXT("WARNING"), MB_OK | MB_SYSTEMMODAL | MB_TOPMOST | MB_ICONEXCLAMATION);
		WinradCallBack(-1, WINRAD_LOCHANGE, 0, NULL);	
		WinradCallBack(-1, WINRAD_LORELEASED, 0, NULL);
		return 2000000000;
	}
	if (freq < (unsigned long)(LowerFqLimit * 1000))
	{
		MessageBox(NULL, "Warning Out of Range", TEXT("WARNING"), MB_OK | MB_SYSTEMMODAL | MB_TOPMOST | MB_ICONEXCLAMATION);
		WinradCallBack(-1, WINRAD_LOCHANGE, 0, NULL);
		WinradCallBack(-1, WINRAD_LORELEASED, 0, NULL);
		return -100000;
	}

	//Code to limit Dialog Box Movement
	Frequency = (double)freq / 1000000;
	while (Frequency >= band_fmin[FreqBand + 1] && FreqBand + 1 < NUM_BANDS)
		FreqBand++;
	LNAMIN = band_LNAgain[FreqBand];
	//SendMessage(GetDlgItem(ghwndDlg, IDC_LNASLIDER), TBM_SETRANGEMIN, (WPARAM)TRUE, (LPARAM)LNAMIN);
	MAXGR = band_MaxGR[FreqBand];
	//SendMessage(GetDlgItem(ghwndDlg, IDC_GAINSLIDER), TBM_SETRANGEMAX, (WPARAM)TRUE, (LPARAM)MAXGR);

	if (Running == FALSE)
	{
		WinradCallBack(-1, WINRAD_LORELEASED, 0, NULL);
		return 0;
	}
	else if (Running == TRUE)
	{
		SDRplayInitalise();
	}
	WinradCallBack(-1, WINRAD_LORELEASED, 0, NULL);
	return 0;
}

extern "C"
int LIBSDRplay_API __stdcall StartHW(unsigned long freq)
{
	if (freq > 2000000000)
	{
		MessageBox(NULL, "Warning Out of Range", TEXT("WARNING"), MB_OK | MB_SYSTEMMODAL | MB_TOPMOST | MB_ICONEXCLAMATION);
		WinradCallBack(-1, WINRAD_LOCHANGE, 0, NULL);
		return -1;
	}
	if (freq < (unsigned long)(LowerFqLimit * 1000))
	{
		MessageBox(NULL, "Warning Out of Range", TEXT("WARNING"), MB_OK | MB_SYSTEMMODAL | MB_TOPMOST | MB_ICONEXCLAMATION);
		WinradCallBack(-1, WINRAD_LOCHANGE, 0, NULL);
		return -1;
	}
	SDRplayInitalise();
	return buffer_len_samples / 2;
}

extern "C"
long LIBSDRplay_API __stdcall GetHWLO()
{
	long returnfreq = (long)( 0.5 + Frequency * 1000000.0 );
	return returnfreq;
}

extern "C"
long LIBSDRplay_API __stdcall GetHWSR()
{
	long SR;

	if (SampleRate[SampleRateIdx].DownSample == 0)
	{
		SR = (long)(SampleRate[SampleRateIdx].SampleRate * 1000000.0);
		if ((((SampleRate[SampleRateIdx].SampleRate == 8.192) && (Bandwidth == mir_sdr_BW_1_536) && (IFMode == mir_sdr_IF_2_048)) ||
			((SampleRate[SampleRateIdx].SampleRate == 2.0) && (Bandwidth == mir_sdr_BW_0_200) && (IFMode == mir_sdr_IF_0_450)) ||
			((SampleRate[SampleRateIdx].SampleRate == 2.0) && (Bandwidth == mir_sdr_BW_0_300) && (IFMode == mir_sdr_IF_0_450)))
		&& down_conversion_enabled)
		{
			SR = SR >> 2;
		}
		if ((SampleRate[SampleRateIdx].SampleRate == 2.0) && (Bandwidth == mir_sdr_BW_0_600) && (IFMode == mir_sdr_IF_0_450) && down_conversion_enabled)
		{
			SR = SR >> 1;
		}
	}
	else
		{
		SR = (long)(SampleRate[SampleRateIdx].SampleRate * 1000000.0);
		SR = SR / SampleRate[SampleRateIdx].DownSample;
		}
	return SR;
}

extern "C"
int LIBSDRplay_API __stdcall ExtIoGetSrates(int srate_idx, double * samplerate)
{
	return 1;	// ERROR
}

extern "C"
int  LIBSDRplay_API __stdcall ExtIoGetActualSrateIdx(void)
{
	return 0;
}

extern "C"
int  LIBSDRplay_API __stdcall ExtIoSetSrate(int srate_idx)
{
	return 1;	// ERROR
}

extern "C"
int  LIBSDRplay_API __stdcall GetAttenuators(int atten_idx, float * attenuation)
{
	return 1;	// ERROR
}

extern "C"
int  LIBSDRplay_API __stdcall GetActualAttIdx(void)
{
	return 0;
}

extern "C"
int  LIBSDRplay_API __stdcall SetAttenuator(int atten_idx)
{
	return 1;	// ERROR
}

extern "C"
int   LIBSDRplay_API __stdcall ExtIoGetAGCs(int agc_idx, char * text)
{
	return 1;	// ERROR
}

extern "C"
int   LIBSDRplay_API __stdcall ExtIoGetActualAGCidx(void)
{
	 return 0;
}

extern "C"
int   LIBSDRplay_API __stdcall ExtIoSetAGC(int agc_idx)
{
	return 1;	// ERROR
}

extern "C"
int   LIBSDRplay_API __stdcall ExtIoGetSetting(int idx, char * description, char * value)
{
	return 1;
}

extern "C"
void  LIBSDRplay_API __stdcall ExtIoSetSetting(int idx, const char * value)
{
	return;
}

extern "C"
void LIBSDRplay_API __stdcall StopHW()
{
	Running = FALSE;
	Stop_Thread();
	mir_sdr_Uninit_fn();
	InitRequired(PostTunerDcCompensation, LOplanAuto, &LOplan, &LOChangeNeeded, Frequency, SampleRate[SampleRateIdx].SampleRate, Bandwidth, IFMode, 1);	//Reset Last Known conditions.
}

extern "C"
void LIBSDRplay_API __stdcall CloseHW()
{
	SaveSettings();
	//if (h_dialog!=NULL)
	//	DestroyWindow(h_dialog);
	//if (h_AdvancedDialog != NULL)
	//	DestroyWindow(h_AdvancedDialog);
}

extern "C"
void LIBSDRplay_API __stdcall ShowGUI()
{
	//if (h_dialog == NULL)
	//	h_dialog = CreateDialog(hInst, MAKEINTRESOURCE(IDD_SDRPLAY_SETTINGS), NULL, (DLGPROC)MainDlgProc);
	//ShowWindow(h_dialog,SW_SHOW);
	//SetForegroundWindow(h_dialog);
}

extern "C"
void LIBSDRplay_API  __stdcall HideGUI()
{
	//ShowWindow(h_dialog,SW_HIDE);
}

extern "C"
void LIBSDRplay_API  __stdcall SwitchGUI()
{
	//if (IsWindowVisible(h_dialog))
	//	ShowWindow(h_dialog,SW_HIDE);
	//else
	//	ShowWindow(h_dialog,SW_SHOW);
}

extern "C"
void LIBSDRplay_API __stdcall SetCallback(void(*myCallBack)(int, int, float, void *))
{
	WinradCallBack = myCallBack;
}

extern "C"
int LIBSDRplay_API __stdcall GetStatus()
{
	return 0;
}

int Start_Thread()
{
    /*
	//If already running, exit
	if (worker_handle != INVALID_HANDLE_VALUE)
	{
		MessageBox(NULL, TEXT("Start Thread return -1"), NULL, MB_OK);
		return -1;
	}

	ThreadExitFlag = 0;
	//Set Threadvariables, Isolates variables in thread from dialog box activity.
	ThreadVariables.SRConverstionFactor = SampleRate[SampleRateIdx].DownSample;
	ThreadVariables.SampleRate = SampleRate[SampleRateIdx].SampleRate;
	ThreadVariables.IFMode = IFMode;
	ThreadVariables.Bandwidth = Bandwidth;
	ThreadVariables.DcOffsetComp = PostTunerDcCompensation;
	worker_handle = (HANDLE)_beginthread((void(*)(void*))ThreadProc, 0, (void*)&ThreadVariables);	
	if (worker_handle == INVALID_HANDLE_VALUE)
	{

		MessageBox(NULL, TEXT("Start Thread return -1"), NULL, MB_OK);
		return -1;
	}
	SetThreadPriority(worker_handle, THREAD_PRIORITY_TIME_CRITICAL);
    */
	return 0;
}

int Stop_Thread()
{
    /*
	if(worker_handle == INVALID_HANDLE_VALUE)
		return -1;
	ThreadExitFlag = 1;
	WaitForSingleObject(worker_handle,INFINITE);
	// CloseHandle(worker_handle);		//  _endthread automatically closes the thread handle!
	worker_handle=INVALID_HANDLE_VALUE;
    */
	return 0;
}

void ThreadProc(ThreadContainer* ThreadVariables)
{
    /*
	// Variables for IQ Readback
	unsigned int FirstSample;
	int grChanged, grchangedstate;
	int rfChanged;
	int fsChanged;
	static int rfchangedstate = 0;

	//variable for Dc offset removal
	short dcoffi = 0;
	short dcoffq = 0;
	short last_dcoffi = 0;
	short last_dcoffq = 0;

	//Variables for AGC Routine
	double Power = 0.0;
	double PowerAve = 0.0;
	int PowerAveCount = 0;
	double setpoint = 0;
	double gRdB = 0.0;
	double sp_p2;
	double sp_m2;

	int Triggered = 0;
	int BufferCounter = 0;
	int DataCount = 0;
	int i;
	mir_sdr_ErrT err;

	int decM = 1;													//Decimation for donconversion
	int SampleCount_Dec = 0;
	int NumberSamples = 0;
	int SRConverstionFactor = 0;

	float *IagcBuffer = NULL;										//Buffers for processing the AGC routine
	float *QagcBuffer = NULL;

	short *xid = NULL;												//Buffers for downconversion
	short *xqd = NULL;

	short *IBuffer = NULL;											//Buffers for Raw Readback data
	short *QBuffer = NULL;

	short *IQBuffer = NULL;											//Buffer for combined IQ Data ready for callback
	short *CallbackBuffer = NULL;									//CallbackD Buffer

	if (IFMode == mir_sdr_IF_Zero)
	{
		if (ThreadVariables->SRConverstionFactor == 0)							//No Samplerate conversion
		{
			DataCount = (SampleCount * 2);
			decM = 1;
		}																				
		else                                                                            //With Samplerate conversion
		{
			DataCount = (SampleCount * 2) / ThreadVariables->SRConverstionFactor;
			decM = 1;
		}
	}
	else
	{
		if ((((ThreadVariables->SampleRate == 8.192) && (ThreadVariables->Bandwidth == mir_sdr_BW_1_536) && (ThreadVariables->IFMode == mir_sdr_IF_2_048)) ||
			((ThreadVariables->SampleRate == 2.0) && (ThreadVariables->Bandwidth == mir_sdr_BW_0_200) && (ThreadVariables->IFMode == mir_sdr_IF_0_450)) ||
			((ThreadVariables->SampleRate == 2.0) && (ThreadVariables->Bandwidth == mir_sdr_BW_0_300) && (ThreadVariables->IFMode == mir_sdr_IF_0_450)))
			 && down_conversion_enabled)
		{
			decM = 4;
			DataCount = (SampleCount >> 2) * 2;
			SampleCount_Dec = SampleCount >> 2;
			xid = (short *)calloc(SampleCount_Dec, sizeof(short));
			if (xid == NULL)
			{
				MessageBox(NULL, TEXT("Downconvert I buffer not allocated"), TEXT("Error!"), MB_OK | MB_ICONERROR);
				goto cleanUpThread;
			}
			xqd = (short *)calloc(SampleCount_Dec, sizeof(short));
			if (xqd == NULL)
			{
				MessageBox(NULL, TEXT("Downconvert Q buffer not allocated"), TEXT("Error!"), MB_OK | MB_ICONERROR);
				goto cleanUpThread;
			}
		}
		if (((ThreadVariables->SampleRate == 2.0) && (ThreadVariables->Bandwidth == mir_sdr_BW_0_600) && (ThreadVariables->IFMode == mir_sdr_IF_0_450)) && down_conversion_enabled)
		{
			decM = 2;
			DataCount = (SampleCount >> 1) * 2;
			SampleCount_Dec = SampleCount >> 1;
			xid = (short *)calloc(SampleCount_Dec, sizeof(short));
			if (xid == NULL)
			{
				MessageBox(NULL, TEXT("Downconvert I buffer not allocated"), TEXT("Error!"), MB_OK | MB_ICONERROR);
				goto cleanUpThread;
			}
			xqd = (short *)calloc(SampleCount_Dec, sizeof(short));
			if (xqd == NULL)
			{
				MessageBox(NULL, TEXT("Downconvert Q buffer not allocated"), TEXT("Error!"), MB_OK | MB_ICONERROR);
				goto cleanUpThread;
			}
		}
	}

	// Initalise Buffers.
	HWND dlg = GetDlgItem(NULL, IDD_SDRPLAY_SETTINGS);

	CallbackBuffer = (short *)calloc((buffer_len_samples), sizeof(short));
	if (CallbackBuffer == NULL)
	{
		MessageBox(NULL, TEXT("Callback buffer not allocated"), TEXT("Error!"), MB_OK | MB_ICONERROR);
		goto cleanUpThread;
	}

	IBuffer = (short *)calloc(SampleCount, sizeof(short));
	if (IBuffer == NULL)
	{
		MessageBox(NULL, TEXT("IBuffer buffer not allocated"), TEXT("Error!"), MB_OK | MB_ICONERROR);
		goto cleanUpThread;
	}

	QBuffer = (short *)calloc(SampleCount, sizeof(short));
	if (QBuffer == NULL)
	{
		MessageBox(NULL, TEXT("QBuffer buffer not allocated"), TEXT("Error!"), MB_OK | MB_ICONERROR);
		goto cleanUpThread;
	}

	IQBuffer = (short *)calloc(DataCount, sizeof(short));
	if (IQBuffer == NULL)
	{
		MessageBox(NULL, TEXT("IQBuffer buffer not allocated"), TEXT("Error!"), MB_OK | MB_ICONERROR);
		goto cleanUpThread;
	}


#if COPY_SAMPLEDATA_TO_AGC_BUFFERS
	IagcBuffer = (float *)calloc(SampleCount, sizeof(float));
	if (IagcBuffer == NULL)
	{
		MessageBox(NULL, TEXT("IagcBuffer buffer not allocated"), TEXT("Error!"), MB_OK | MB_ICONERROR);
		goto cleanUpThread;
	}
	QagcBuffer = (float *)calloc(SampleCount, sizeof(float));
	if (QagcBuffer == NULL)
	{
		MessageBox(NULL, TEXT("QagcBuffer buffer not allocated"), TEXT("Error!"), MB_OK | MB_ICONERROR);
		goto cleanUpThread;
	}
#endif

	//Loop for reading packets.
	rfchangedstate = -2;
	grchangedstate = -2;
	Running = TRUE;
	while (ThreadExitFlag == 0)
	{
		err = mir_sdr_ReadPacket_fn(&IBuffer[0], &QBuffer[0], &FirstSample, &grChanged, &rfChanged, &fsChanged);
		if (rfChanged == 1)
		{
			rfchangedstate = !rfchangedstate;
			ThreadVariables->RfToggle = rfchangedstate;

		}
		if (grChanged == 1)
		{
			grchangedstate = !grchangedstate;
			ThreadVariables->GrToggle = grchangedstate;
		}

		if (decM != 1)
		{
			mir_sdr_DownConvert_fn(&IBuffer[0], &xid[0], &xqd[0], SampleCount, ThreadVariables->IFMode, decM, 0);
			int j = 0;
			for (i = 0; i < SampleCount_Dec; i++)
			{
				IQBuffer[j++] = xid[i];
				IQBuffer[j++] = xqd[i];
			}
		}
		else
		{	
			//Post tuner DC Offset Compensation
			if (ThreadVariables->DcOffsetComp == TRUE)
			{
				//OutputDebugString("DC Compensation Enabled");
				for (i = 0; i < SampleCount; ++i)
				{
					dcoffi = last_dcoffi + DcRemovalFilterCoef * (IBuffer[i] - last_dcoffi);
					dcoffq = last_dcoffq + DcRemovalFilterCoef * (QBuffer[i] - last_dcoffq);
					last_dcoffi = dcoffi;
					last_dcoffq = dcoffq;
				}

				for (i = 0; i < SampleCount; ++i)
				{
					IBuffer[i] -= dcoffi;
					QBuffer[i] -= dcoffq;
				}
			}

			//No Samplerate Conversion
			if (ThreadVariables->SRConverstionFactor == 0)
			{
				int j = 0;
				for (i = 0; i < SampleCount; ++i)
				{
					IQBuffer[j++] = IBuffer[i];
					IQBuffer[j++] = QBuffer[i];
				}
			}
			//Samplerate Conversion
			if (ThreadVariables->SRConverstionFactor != 0)
			{
				int j = 0;
				for (i = 0; i < SampleCount; ++i)
				{
					IQBuffer[j++] = IBuffer[i];
					IQBuffer[j++] = QBuffer[i];
					i = i + (ThreadVariables->SRConverstionFactor - 1);
				}
			}
		}

		//Fill the callback buffer
		for (i = 0; i < DataCount;)
		{
			if (BufferCounter == 0 && i + DataCount >= buffer_len_samples)
			{
				// no need to copy, if CallbackBuffer empty and i .. i+buffer_len_samples <= DataCount
				// this case looks impossible when DataCount = 504 !
				WinradCallBack(buffer_len_samples / 2, 0, 0, (void*)(&IQBuffer[i]));
				i += buffer_len_samples;
			}
			else if (BufferCounter + DataCount >= buffer_len_samples)
			{
				// CallbackBuffer[] will be filled => check if WinradCallBack() is to be called
				for (; i < DataCount; i++)
				{
					CallbackBuffer[BufferCounter++] = IQBuffer[i];
					if (BufferCounter == buffer_len_samples)
					{
						WinradCallBack(buffer_len_samples / 2, 0, 0, (void*)CallbackBuffer);
						BufferCounter = 0;
					}
				}
			}
			else // if (BufferCounter + DataCount < buffer_len_samples)
			{
				// no chance to fill CallbackBuffer[] => avoid unnecessary if's
				for (; i < DataCount; i++)
					CallbackBuffer[BufferCounter++] = IQBuffer[i];
			}
		}

		// Process AGC based on samples retried from mir_sdr_ReadPacket_fn
		// Configure the setpoint for the AGC routine
		setpoint = pow(10, (double)(AGCsetpoint / 10.0));					//convert setpoint to a voltage and scale for ADC range.
		sp_p2 = pow(10, (double)((AGCsetpoint + 2) / 10.0));				// only modify if outside +/2dB
		sp_m2 = pow(10, (double)((AGCsetpoint - 2) / 10.0));

		if (AGCEnabled)
		{
#if COPY_SAMPLEDATA_TO_AGC_BUFFERS
			for (i = 0; i < SampleCount; i++)
			{
				IagcBuffer[i] = (float)IBuffer[i] * ONE_OVER_32768;
				QagcBuffer[i] = (float)QBuffer[i] * ONE_OVER_32768;
			}
#endif

			{

#if COPY_SAMPLEDATA_TO_AGC_BUFFERS
				for (i = 0; i < SampleCount; i++)
					Power += (double)(IagcBuffer[i] * IagcBuffer[i]) + (double)(QagcBuffer[i] * QagcBuffer[i]);
#else

				for (i = 0; i < SampleCount; i++)
					Power += (float)IBuffer[i] * (float)IBuffer[i] + (float)QBuffer[i] * (float)QBuffer[i];
				Power /= ( 32768.0 * 32768.0 );		// normalize power
#endif
				Power /= SampleCount;
				PowerAve += Power;
				PowerAveCount++;
				if (PowerAveCount == 2000)
				{
					PowerAve = PowerAve / 2000;
					if ((PowerAve > sp_p2) || (PowerAve < sp_m2))
					{
						gRdB = 10 * log10(PowerAve / setpoint);
						gRdB += (gRdB >= 0.0) ? 0.5 : -0.5;
						mir_sdr_SetGr_fn((int)gRdB, 0, 0);
						GainReduction += (int)gRdB;
						if (GainReduction >= 102)
							GainReduction = 102;
						else if (GainReduction <= 0)
							GainReduction = 0;
					}
					PowerAveCount = 0;
					PowerAve = 0.0;
				}
			}
		}
	}

cleanUpThread:
	// avoid memory leaks!
	free(CallbackBuffer);
	free(IBuffer);
	free(QBuffer);
	free(xid);
	free(xqd);
	free(IagcBuffer);
	free(QagcBuffer);
	free(IQBuffer);

	_endthread();
    */
}

void SDRplayInitalise()
{
	mir_sdr_ErrT err;
	TCHAR str[255];
	double NominalFreqency;
	int programmed = 0;
	static int LastRfToggle = -1;
	static int LastDcCompenastionMode = -1;
	
	NominalFreqency = Frequency * (1.0E6 + FqOffsetPPM) * 1.0E-6;	// including ppm correction
	if ((InitRequired(PostTunerDcCompensation, LOplanAuto, &LOplan, &LOChangeNeeded, NominalFreqency, SampleRateIdx, Bandwidth, IFMode, 0) == TRUE) || (Running == FALSE))
		{
			#if DEBUG
			OutputDebugString("Full Tune Required");
			#endif 
			Running = FALSE;
			Stop_Thread();									//Stop Thread, if there is one
			err = mir_sdr_Uninit_fn();						//Stop hardware for new init
			if (LOChangeNeeded == TRUE)
			{
				err = mir_sdr_SetParam_fn(101, LOplan);
				if (err != mir_sdr_Success)
				{
					sprintf_s(str, sizeof(str), "Failed to Apply LO Plan");
					MessageBox(NULL, str, TEXT("SDRplay ExtIO DLL"), MB_ICONERROR | MB_OK);
				}
			}
			err = mir_sdr_Init_fn(GainReduction, SampleRate[SampleRateIdx].SampleRate, NominalFreqency, Bandwidth, IFMode, &SampleCount);
			mir_sdr_SetDcMode_fn(DcCompensationMode, 0);
			mir_sdr_SetGrParams_fn(0, LNAGRTHRES);			//Apply Old LNA Threshold
			mir_sdr_SetGr_fn(GainReduction, 1, 0);			//Reapply GR so new LNA Thres takes effect.
			Start_Thread();
		}
		else
		{
			// Program Frequency Change
			if (lastFreq != NominalFreqency)
			{
				programmed = 0;
				int count = 0;
				while (programmed == 0)
				{
					if (ThreadVariables.RfToggle == LastRfToggle)
					{
						programmed = 0; 
						Sleep(25);
						if (count == 4)
						{
							LastRfToggle = -1;
						}						
						count++;
					}
					else
					{
						err = mir_sdr_SetRf_fn(NominalFreqency*1.0E6, 1, 0);
						programmed = 1;
						LastRfToggle = ThreadVariables.RfToggle;
					}
				}
			}

			//Program Gain Reduction.
			if (lastLNAGRTHRES != LNAGRTHRES)
			{
				err = mir_sdr_SetGrParams_fn(0, LNAGRTHRES);
			}

			//Program DC Compensation.
			if (LastDcCompenastionMode != DcCompensationMode)
			{
				mir_sdr_SetDcMode_fn(DcCompensationMode, 0);
				mir_sdr_SetDcTrackTime_fn(TrackingPeriod);
			}

			//Program Gain Reduction.
			if (lastGainReduction != GainReduction || lastLNAGRTHRES != LNAGRTHRES || LastDcCompenastionMode != DcCompensationMode)
			{
				programmed = 0;
				int count = 0;
				while (programmed == 0)
				{
					if (ThreadVariables.GrToggle == LastGrToggle)
					{
						programmed = 0;
						Sleep(25);
						if (count == 4)
						{
							LastGrToggle = -1;
						}
						count++;
					}
					else
					{
						err = mir_sdr_SetGr_fn(GainReduction, 1, 0);
						if (err == mir_sdr_Success)
						{
							programmed = 1;
							LastGrToggle = ThreadVariables.GrToggle;
						}
					}
				}
			}
		}
		lastFreq = NominalFreqency;
		lastLNAGRTHRES = LNAGRTHRES;
		lastGainReduction = GainReduction;
		LastDcCompenastionMode = DcCompensationMode;
}

int FindSampleRateIdx(double WantedSampleRate)
{
	int Found, i, SRiD;
	double SR;

	Found = 0;
	for (i = 0; i < (sizeof(SampleRate) / sizeof(SampleRate[0]))-1; i++)
	{
		SR = (SampleRate[i].DisplayValue) + 0.01;
		if (SR >  WantedSampleRate && Found == 0)
		{
			SRiD = i;
			Found = 1;
		}
	}
	return SRiD;
}

bool InitRequired(bool PostDcComp, bool LOAuto, int *LOFrequency, bool *LOChangeNeeded, double Frequency, double SampleRateID, mir_sdr_Bw_MHzT BW, mir_sdr_If_kHzT IF, int RST)
{
	bool InitRequired = FALSE;
	int FreqBand = 0;
	static bool lastLoAuto = false;
	static bool lastPostDcComp = false;
	static int LastFreqBand = -1;
	static int LastLOFrequency = -1;
	static double LastFrequency = -1;
	static int LOBand = -1;
	static int LastLOBand = -1;
	static double LastSampleRateID = -1;
	static mir_sdr_Bw_MHzT LastBW;
	static mir_sdr_If_kHzT LastIF;

	//LO Profiles			    0				1				2			
	const double LO_fmin[3] = { 250, 375, 395.0 };
	const double LO_fmax[3] = { 374.999999, 394.999999, 419.999999 };
	const int	 fLO[3]		= { LO120MHz, LO144MHz, LO168MHz };

	//Frequency Bands
	#define NUM_BANDS	8     //	 0			1			2		  3			  4			  5	          6			  7			
	const double fmin[NUM_BANDS] = { 0.1,		12.0,	   30.0,	  60.0,		  120.0,	  250.0,	  420.0,	  1000.0 };
	const double fmax[NUM_BANDS] = { 11.999999, 29.999999, 59.999999, 119.999999, 249.999999, 419.999999, 999.999999, 2000.0 };

	//Redefine Defaults
	InitRequired = FALSE;
	*LOChangeNeeded = FALSE;

	//Reset lastknown conditions
	if (RST == 1)
	{
		LastFreqBand = -1;
		LastLOFrequency = -1;
		LastFrequency = -1;
		LastLOBand = -1;
		LastSampleRateID = -1;
		return InitRequired;
	}

	//Change in Post DC COmpensation requires an Init to start thread again
	if (lastPostDcComp != PostDcComp)
		InitRequired = TRUE;

	//Chanage in Freqeuncy Band require an initalisation
	FreqBand = 0;
	while (Frequency > fmax[FreqBand] && FreqBand < NUM_BANDS)
		++FreqBand;
	if (FreqBand != LastFreqBand)
	{
		InitRequired = TRUE;
	}

	//Changed as winradcallback has been implemented insterad.  Exectuing stop and start should not require a new Init.
	//Changes in Sample rate or IF Bandwidth require an initalisation
	if ((SampleRateID != LastSampleRateID) || (IF != LastIF) || (BW != LastBW))
	{
		InitRequired = TRUE;
	}

	//If we have moved from fixed LO to auto LO in any mode apply correct Auto LO mode
	if ((lastLoAuto == FALSE) && (LOAuto == TRUE))
	{
		if (Frequency < fmin[3])
		{
			*LOFrequency = LO120MHz;
			InitRequired = TRUE;
			*LOChangeNeeded = TRUE;
		}
		if ((Frequency > fmax[4]) && (Frequency < fmin[6]))
		{
			while (Frequency > LO_fmax[LOBand] && LOBand < 3)
				++LOBand;
			*LOFrequency = fLO[LOBand];
		}
	}
	
	// IF below 60MHz and in a different frequency band Init and apply LO again.  If in AUTO reset LO to 120MHz else leave LO setting alone
	if ((FreqBand != LastFreqBand) && (Frequency < fmin[3]))
	{
		InitRequired = TRUE;
		*LOChangeNeeded = TRUE;
		if (LOAuto == TRUE)
		{
			*LOFrequency = LO120MHz;
		}

	}

	//If not in auto mode and LO plan changes then init.
	//if ((LOAuto == FALSE) && (*LOFrequency != LastLOFrequency))
	if (*LOFrequency != LastLOFrequency)
	{
		InitRequired = TRUE;
		*LOChangeNeeded = TRUE;	
	}

	//When LO is set to Auto selects correct LOplan for 250 - 419 Frequency Range.
	if ((Frequency > fmax[4]) && (Frequency < fmin[6]))
	{
		LOBand = 0;
		while (Frequency > LO_fmax[LOBand] && LOBand < 3)
			++LOBand;
		if ((LOBand != LastLOBand) || (FreqBand != LastFreqBand))
		{
			InitRequired = TRUE;
			*LOChangeNeeded = TRUE;
			if (LOAuto == TRUE)
			{
				*LOFrequency = fLO[LOBand];
			}
		}
	}

	LastFrequency = Frequency;
	LastLOFrequency = *LOFrequency;
	LastFreqBand = FreqBand;
	LastLOBand = LOBand;
	LastSampleRateID = SampleRateID;
	LastIF = IF;
	LastBW = BW;
	lastLoAuto = LOAuto;
	lastPostDcComp = PostDcComp;
	return InitRequired;
}

char FreqoffsetTxt[256];
char LNAGRTHRESTtxt[256];
char GainReductionTxt[256];
char AGCsetpointTxt[256];

void SaveSettings()
{
    /*
	HKEY Settingskey;
	int error, AGC, LOAuto, PostDcComp;
	DWORD dwDisposition;

	error = RegOpenKeyEx(HKEY_CURRENT_USER, TEXT("Software\\SDRplay\\Settings"), 0, KEY_ALL_ACCESS, &Settingskey);
	if (error != ERROR_SUCCESS)
	{ 
		if (error == ERROR_FILE_NOT_FOUND)
		{
			//Need to create registry entry.
			error = RegCreateKeyEx(HKEY_CURRENT_USER, TEXT("Software\\SDRplay\\Settings"), 0, NULL, 0, KEY_ALL_ACCESS, NULL, &Settingskey, &dwDisposition);
		}
		else
		{
			MessageBox(NULL, "Failed to locate Settings registry entry", NULL, MB_OK);
		}
	}

	error = RegSetValueEx(Settingskey, TEXT("DcCompensationMode"), 0, REG_DWORD, (const BYTE*)&DcCompensationMode, sizeof(DcCompensationMode));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save DcCompensationMode", NULL, MB_OK);

	error = RegSetValueEx(Settingskey, TEXT("RefreshPeriodMemory"), 0, REG_DWORD, (const BYTE*)&RefreshPeriodMemory, sizeof(DcCompensationMode));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save RefreshPeriodMemory", NULL, MB_OK);

	error = RegSetValueEx(Settingskey, TEXT("TrackingPeriod"), 0, REG_DWORD, (const BYTE*)&TrackingPeriod, sizeof(TrackingPeriod));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save TrackingPeriod", NULL, MB_OK);

	error = RegSetValueEx(Settingskey, TEXT("LNAGR"), 0, REG_DWORD, (const BYTE*)&LNAGRTHRES, sizeof(LNAGRTHRES));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save LNA Threshold", NULL, MB_OK);

	error = RegSetValueEx(Settingskey, TEXT("FreqTrim"), 0, REG_DWORD, (const BYTE*)&FqOffsetPPM, sizeof(FqOffsetPPM));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save Frequenct Trim", NULL, MB_OK);

	error = RegSetValueEx(Settingskey, TEXT("IFmodeIdx"), 0, REG_DWORD, (const BYTE*)&IFmodeIdx, sizeof(IFmodeIdx));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save IF Mode", NULL, MB_OK);

	error = RegSetValueEx(Settingskey, TEXT("BandwidthIdx"), 0, REG_DWORD, (const BYTE*)&BandwidthIdx, sizeof(BandwidthIdx));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save IF Bandwidth", NULL, MB_OK);

	error = RegSetValueEx(Settingskey, TEXT("SampleRateIdx"), 0, REG_DWORD, (const BYTE*)&SampleRateIdx, sizeof(SampleRateIdx));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save Sample Rate", NULL, MB_OK);

	error = RegSetValueEx(Settingskey, TEXT("SampleRateDisplayIdx"), 0, REG_DWORD, (const BYTE*)&SampleRateDisplayIdx, sizeof(SampleRateDisplayIdx));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save Sample Rate", NULL, MB_OK);

	error = RegSetValueEx(Settingskey, TEXT("AGCsetpoint"), 0, REG_DWORD, (const BYTE*)&AGCsetpoint, sizeof(AGCsetpoint));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save AGC Setpoint", NULL, MB_OK);

	error = RegSetValueEx(Settingskey, TEXT("GainReduction"), 0, REG_DWORD, (const BYTE*)&GainReduction, sizeof(GainReduction));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save Gain Reduction", NULL, MB_OK);

	error = RegSetValueEx(Settingskey, TEXT("LOplan"), 0, REG_DWORD, (const BYTE*)&LOplan, sizeof(LOplan));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save LO Plan", NULL, MB_OK);

	error = RegSetValueEx(Settingskey, TEXT("Frequency"), 0, REG_BINARY, (const BYTE*)&Frequency, sizeof(Frequency));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save Frequency", NULL, MB_OK);

	if (AGCEnabled == TRUE)
		AGC = 1;
	else
		AGC = 0;
	error = RegSetValueEx(Settingskey, TEXT("AGCEnabled"), 0, REG_DWORD, (const BYTE*)&AGC, sizeof(AGC));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save AGC Setting", NULL, MB_OK);

	if (LOplanAuto == TRUE)
		LOAuto = 1;
	else
		LOAuto = 0;
	error = RegSetValueEx(Settingskey, TEXT("LOAuto"), 0, REG_DWORD, (const BYTE*)&LOAuto, sizeof(LOAuto));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save LO Auto Setting", NULL, MB_OK);

	if (PostTunerDcCompensation == TRUE)
		PostDcComp = 1;
	else
		PostDcComp = 0;
	error = RegSetValueEx(Settingskey, TEXT("PostDCComp"), 0, REG_DWORD, (const BYTE*)&PostDcComp, sizeof(PostDcComp));
	if (error != ERROR_SUCCESS)
		MessageBox(NULL, "Failed to save Post DC Compensation Setting", NULL, MB_OK);

	RegCloseKey(Settingskey);
    */
}

void LoadSettings()
{
    /*
	HKEY Settingskey;
	int error, tempRB;
	DWORD DoubleSz, IntSz;

	DoubleSz = sizeof(double);
	IntSz = sizeof(int);

	error = RegOpenKeyEx(HKEY_CURRENT_USER, TEXT("Software\\SDRplay\\Settings"), 0, KEY_ALL_ACCESS, &Settingskey);
	if (error == ERROR_SUCCESS)
	{
		error = RegQueryValueEx(Settingskey, "LowerFqLimit", NULL, NULL, (LPBYTE)&LowerFqLimit, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Lower Frequency Limit set to 100kHz");
			LowerFqLimit = 100;
		}

		error = RegQueryValueEx(Settingskey, "DcCompensationMode", NULL, NULL, (LPBYTE)&DcCompensationMode, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall DcCompensationMode");
			DcCompensationMode = 3;
		}

		error = RegQueryValueEx(Settingskey, "RefreshPeriodMemory", NULL, NULL, (LPBYTE)&RefreshPeriodMemory, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall Refresh Period");
			RefreshPeriodMemory = 2;
		}

		error = RegQueryValueEx(Settingskey, "TrackingPeriod", NULL, NULL, (LPBYTE)&TrackingPeriod, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall DC Compensation Tracking Period");
			TrackingPeriod = 20;
		}

		error = RegQueryValueEx(Settingskey, "Frequency", NULL, NULL, (LPBYTE)&Frequency, &DoubleSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall saved frequency state");
			Frequency = 98.8;
		}

		error = RegQueryValueEx(Settingskey, "LOplan", NULL, NULL, (LPBYTE)&LOplan, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall saved LO Plan");
			LOplan = LO120MHz;
		}

		error = RegQueryValueEx(Settingskey, "GainReduction", NULL, NULL, (LPBYTE)&GainReduction, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall saved Gain Reduction");
			GainReduction = 50;
		}

		error = RegQueryValueEx(Settingskey, "AGCsetpoint", NULL, NULL, (LPBYTE)&AGCsetpoint, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall saved AGC Setpoint");
			AGCsetpoint = -15;
		}

		error = RegQueryValueEx(Settingskey, "SampleRateIdx", NULL, NULL, (LPBYTE)&SampleRateIdx, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall saved SampleRateIdx");
			SampleRateIdx = 8;
		}

		error = RegQueryValueEx(Settingskey, "SampleRateDisplayIdx", NULL, NULL, (LPBYTE)&SampleRateDisplayIdx, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall saved SampleRateDisplayIdx");
			SampleRateDisplayIdx = 0;
		}

		error = RegQueryValueEx(Settingskey, "BandwidthIdx", NULL, NULL, (LPBYTE)&BandwidthIdx, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall saved BandwidthIdx");
			BandwidthIdx = 3;
		}

		error = RegQueryValueEx(Settingskey, "IFmodeIdx", NULL, NULL, (LPBYTE)&IFmodeIdx, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall saved IFmodeIdx");
			IFmodeIdx = 0;
		}

		error = RegQueryValueEx(Settingskey, "FreqTrim", NULL, NULL, (LPBYTE)&FqOffsetPPM, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall saved FreqTrim");
			FqOffsetPPM = 0;
		}

		error = RegQueryValueEx(Settingskey, "LNAGR", NULL, NULL, (LPBYTE)&LNAGRTHRES, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall saved LNAGR state");
			LNAGRTHRES = 59;
		}

		error = RegQueryValueEx(Settingskey, "AGCEnabled", NULL, NULL, (LPBYTE)&tempRB, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall saved AGCEnabled state");
			AGCEnabled = TRUE;
		}
		if (tempRB == 1)
			AGCEnabled = TRUE;
		else
			AGCEnabled = FALSE;

		error = RegQueryValueEx(Settingskey, "LOAuto", NULL, NULL, (LPBYTE)&tempRB, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall saved LOAuto state");
			LOplanAuto = TRUE;
		}
		if (tempRB == 1)
			LOplanAuto = TRUE;
		else
			LOplanAuto = FALSE;

		error = RegQueryValueEx(Settingskey, "PostDCComp", NULL, NULL, (LPBYTE)&tempRB, &IntSz);
		if (error != ERROR_SUCCESS)
		{
			OutputDebugString("Failed to recall saved Post DC Compensation state");
			PostTunerDcCompensation = TRUE;
		}
		if (tempRB == 1)
			PostTunerDcCompensation = TRUE;
		else
			PostTunerDcCompensation = FALSE;
	}
	else
        */
	{
		//If cannot find any registry settings loads some appropriate defaults
		DcCompensationMode = 3;
		TrackingPeriod = 20;
		RefreshPeriodMemory = 2;
		Frequency = 98.8;
		LOplan = LO120MHz;
		GainReduction = 50;
		AGCsetpoint = -15;
		SampleRateIdx = 8;
		SampleRateDisplayIdx = 0;
		BandwidthIdx = 3;
		IFmodeIdx = 0;
		FqOffsetPPM = 0;
		LNAGRTHRES = 59;
		AGCEnabled = TRUE;
		LOplanAuto = TRUE;
		PostTunerDcCompensation = TRUE;
	}

	//RegCloseKey(Settingskey);
}

/*
static INT_PTR CALLBACK MainDlgProc(HWND hwndDlg, UINT uMsg, WPARAM wParam, LPARAM lParam)
	{
	static HWND hGain;
	static HBRUSH BRUSH_RED = CreateSolidBrush(RGB(255, 0, 0));
	static HBRUSH BRUSH_GREEN = CreateSolidBrush(RGB(0, 255, 0));

	TCHAR str[255];
	int FreqBand = 0;

	switch (uMsg)
		{
		case WM_TIMER:
			if (GainReduction >= 102)
			{
				GainReduction = 102;
			}
			_stprintf_s(str, 255, TEXT("%d"), GainReduction);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_GR), 1);
			SendMessage(GetDlgItem(hwndDlg, IDC_GR), WM_SETTEXT, (WPARAM)0, (LPARAM)str);				
			Edit_Enable(GetDlgItem(hwndDlg, IDC_GR), 0);

			Edit_Enable(GetDlgItem(hwndDlg, IDC_GAINSLIDER), 1);
			SendMessage(GetDlgItem(hwndDlg, IDC_GAINSLIDER), TBM_SETPOS, (WPARAM)TRUE, (LPARAM)GainReduction);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_GAINSLIDER), 0);

			while (Frequency > band_fmin[FreqBand + 1] && FreqBand + 1 < NUM_BANDS)
				FreqBand++;

			//LNA On
			if (GainReduction <= LNAGRTHRES)
			{
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGR), "LNA GR 0 dB");
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LNASTATE), "LNA ON");
				sprintf_s(str, sizeof(str), "IF Gain Reduction %d dB", GainReduction);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_IFGR), str);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_MIXERGR), "Mixer GR 0 dB");
				Edit_SetText(GetDlgItem(hwndDlg, IDC_MXRSTATE), "MIXER ON");
			}

			//LNA OFF
			if (GainReduction > LNAGRTHRES)
			{
				sprintf_s(str, sizeof(str), "LNA GR %d dB", band_LNAgain[FreqBand]);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGR), str);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LNASTATE), "LNA OFF");
				sprintf_s(str, sizeof(str), "IF Gain Reduction %d dB", GainReduction - band_LNAgain[FreqBand]);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_IFGR), str);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_MIXERGR), "Mixer GR 0 dB");
				Edit_SetText(GetDlgItem(hwndDlg, IDC_MXRSTATE), "MIXER ON");
			}

			//Mixer OFF
			if (GainReduction > (band_MaxGR[FreqBand] - band_MIXgain[FreqBand]))
			{
				sprintf_s(str, sizeof(str), "LNA GR %d dB", band_LNAgain[FreqBand]);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGR), str);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LNASTATE), "LNA OFF");
				sprintf_s(str, sizeof(str), "Mixer GR %d dB", band_MIXgain[FreqBand]);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_MIXERGR), str);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_MXRSTATE), "MIXER OFF");
				sprintf_s(str, sizeof(str), "IF Gain Reduction %d dB", GainReduction - band_LNAgain[FreqBand] - band_MIXgain[FreqBand]);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_IFGR), str);
			}

			break;

		case WM_NOTIFY:
			break;

		case WM_SYSCOMMAND:
			switch (wParam & 0xFFF0)
			{
				case SC_SIZE:
				case SC_MINIMIZE:
				case SC_MAXIMIZE:
				return TRUE;
			}
			break;

		case WM_CLOSE:
			ShowWindow(h_dialog, SW_HIDE);
			if (h_AdvancedDialog != NULL)
				ShowWindow(h_AdvancedDialog, SW_HIDE);
			return TRUE;
			break;

		case WM_DESTROY:
			h_dialog = NULL;
			return TRUE;
			break;

		case WM_VSCROLL:
			if ((HWND)lParam == GetDlgItem(hwndDlg, IDC_LNASLIDER))
			{
				int pos = SendMessage(GetDlgItem(hwndDlg, IDC_LNASLIDER), TBM_GETPOS, (WPARAM)0, (LPARAM)0);
				sprintf_s(LNAGRTHRESTtxt, 254, "%d", pos);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGRTHRES), LNAGRTHRESTtxt);
				LNAGRTHRES = pos;

				//Update Text to reflect new LNA Slider position
				while (Frequency > band_fmin[FreqBand + 1] && FreqBand + 1 < NUM_BANDS)
					FreqBand++;

				//LNA On
				if (GainReduction < LNAGRTHRES)
				{
					Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGR), "LNA GR 0 dB");
					Edit_SetText(GetDlgItem(hwndDlg, IDC_LNASTATE), "LNA ON");
					sprintf_s(str, sizeof(str), "IF Gain Reduction %d dB", GainReduction);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_IFGR), str);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_MIXERGR), "Mixer GR 0 dB");
					Edit_SetText(GetDlgItem(hwndDlg, IDC_MXRSTATE), "MIXER ON");
				}

				//LNA OFF
				if (GainReduction >= LNAGRTHRES)
				{
					sprintf_s(str, sizeof(str), "LNA GR %d dB", band_LNAgain[FreqBand]);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGR), str);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_LNASTATE), "LNA OFF");
					sprintf_s(str, sizeof(str), "IF Gain Reduction %d dB", GainReduction - band_LNAgain[FreqBand]);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_IFGR), str);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_MIXERGR), "Mixer GR 0 dB");
					Edit_SetText(GetDlgItem(hwndDlg, IDC_MXRSTATE), "MIXER ON");
				}

				//Mixer OFF
				if (GainReduction > (band_MaxGR[FreqBand] - band_MIXgain[FreqBand]))
				{
					sprintf_s(str, sizeof(str), "LNA GR %d dB", band_LNAgain[FreqBand]);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGR), str);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_LNASTATE), "LNA OFF");
					sprintf_s(str, sizeof(str), "Mixer GR %d dB", band_MIXgain[FreqBand]);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_MIXERGR), str);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_MXRSTATE), "MIXER OFF");
					sprintf_s(str, sizeof(str), "IF Gain Reduction %d dB", GainReduction - band_LNAgain[FreqBand] - band_MIXgain[FreqBand]);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_IFGR), str);
				}
	
				return TRUE;
			}
			if ((HWND)lParam == GetDlgItem(hwndDlg, IDC_GAINSLIDER))
			{
				int FreqBand = 0;
				TCHAR str1[255] = "dB";

				int pos = SendMessage(GetDlgItem(hwndDlg, IDC_GAINSLIDER), TBM_GETPOS, (WPARAM)0, (LPARAM)0);
				GainReduction = pos;
				sprintf_s(GainReductionTxt, 254, "%d", pos);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_GR), GainReductionTxt);
				return TRUE;
			}
			break;

		case WM_INITDIALOG:
			// Buffer size

			ghwndDlg = hwndDlg;
			int SrCount;
			double SR, BW;
			TCHAR SampleRateTxt[255];

			LoadSettings();
			//Buffer Size (currently not used)
			for (int i = 0; i < (sizeof(buffer_sizes) / sizeof(buffer_sizes[0])); i++)  //Work out the size of the buffer.
			{
				_stprintf_s(str, 255, TEXT("%d kB"), buffer_sizes[i]);
				ComboBox_AddString(GetDlgItem(hwndDlg, IDC_BUFFER), str);
			}
			ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_BUFFER), buffer_default);
			buffer_len_samples = buffer_sizes[buffer_default] * 1024;

			//Add IF mode strings and select stored IF mode
			_stprintf_s(str, 255, "Zero IF");
			ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFMODE), str);
			_stprintf_s(str, 255, "Low IF");
			ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFMODE), str);
			ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_IFMODE), IFmodeIdx);

			//Add Filter BW based on IF mode Selection then select stored BW.
			if (IFmodeIdx == 0)
			{
				IFMode = mir_sdr_IF_Zero;
				ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_IFBW));
				_stprintf_s(str, 255, "200 kHz");
				ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
				_stprintf_s(str, 255, "300 kHz");
				ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
				_stprintf_s(str, 255, "600 kHz");
				ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
				_stprintf_s(str, 255, "1.536 MHz");
				ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
				_stprintf_s(str, 255, "5.000 MHz");
				ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
				_stprintf_s(str, 255, "6.000 MHz");
				ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
				_stprintf_s(str, 255, "7.000 MHz");
				ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
				_stprintf_s(str, 255, "8.000 MHz");
				ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
				ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_IFBW), BandwidthIdx);
			}
			else
			{
				ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_IFBW));
				_stprintf_s(str, 255, "200 kHz");
				ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
				_stprintf_s(str, 255, "300 kHz");
				ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
				_stprintf_s(str, 255, "600 kHz");
				ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
				_stprintf_s(str, 255, "1.536 MHz");
				ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
				ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_IFBW), BandwidthIdx);
			}	
			BandwidthIdx = ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_IFBW), BandwidthIdx);
			Bandwidth = bandwidths[BandwidthIdx].bwType;

			//Add Samplerates based Filter BW  & IF mode then select stored Samplerate.
			if (IFmodeIdx == 1)
			{
				//LIF Mode
				if (Bandwidth == mir_sdr_BW_1_536)
				{
					IFMode = mir_sdr_IF_2_048;
					ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_SAMPLERATE));
					_stprintf_s(str, 255, TEXT("%.2f"), SampleRate[SampleRateIdx].DisplayValue);
					ComboBox_AddString(GetDlgItem(hwndDlg, IDC_SAMPLERATE), str);
					ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_SAMPLERATE), 0);
				}
				if (Bandwidth == mir_sdr_BW_0_200 || Bandwidth == mir_sdr_BW_0_300 || Bandwidth == mir_sdr_BW_0_600)
				{
					IFMode = mir_sdr_IF_0_450;
					ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_SAMPLERATE));
					_stprintf_s(str, 255, TEXT("%.2f"), SampleRate[SampleRateIdx].DisplayValue);
					ComboBox_AddString(GetDlgItem(hwndDlg, IDC_SAMPLERATE), str);
					ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_SAMPLERATE), 0);
				}
			}
			else
			{
				//ZIF Mode
				SrCount = (sizeof(SampleRate) / sizeof(SampleRate[0])) - 1;

				//calculate minimum SampleRate for stored BW & IF Settings
				BW = (float)bandwidths[BandwidthIdx].BW;
				//Note Minimum sample rate in IF mode is BW/2 * 2 which is BW.
				//MinSRf = 2 * (IFBW + (BW / 2));

				//Add Sample rates to dialog box based on calculated Minimum & identify chosen rate on way through.
				ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_SAMPLERATE));
				for (int i = 0; i < SrCount; i++)
				{
					SR = SampleRate[i].DisplayValue + 0.01;
					if (SR > BW)   //BW = minimum sample rate.
					{
						_stprintf_s(str, 255, TEXT("%.2f"), SampleRate[i].DisplayValue);
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_SAMPLERATE), str);								
					}
				}
				ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_SAMPLERATE), SampleRateDisplayIdx);
			}

			//Gain Reduction
			sprintf_s(GainReductionTxt, 254, "%d", GainReduction);
			SendMessage(GetDlgItem(hwndDlg, IDC_GR_S), UDM_SETRANGE, (WPARAM)TRUE, 102 | (2 << 16));
			SendMessage(GetDlgItem(hwndDlg, IDC_GAINSLIDER), TBM_SETRANGEMIN, (WPARAM)TRUE, (LPARAM)0);
			SendMessage(GetDlgItem(hwndDlg, IDC_GAINSLIDER), TBM_SETRANGEMAX, (WPARAM)TRUE, (LPARAM)102);
			SendMessage(GetDlgItem(hwndDlg, IDC_GAINSLIDER), TBM_SETPOS, (WPARAM)TRUE, (LPARAM)GainReduction);
			Edit_SetText(GetDlgItem(hwndDlg, IDC_GR), GainReductionTxt);

			//ADC Setpoint
			sprintf_s(AGCsetpointTxt, 254, "%d", AGCsetpoint);
			SendMessage(GetDlgItem(hwndDlg, IDC_SETPOINT_S), UDM_SETRANGE, (WPARAM)TRUE, 0 | (-50 << 16));
			Edit_SetText(GetDlgItem(hwndDlg, IDC_SETPOINT), AGCsetpointTxt);

			//Frequency Offset
			sprintf_s(FreqoffsetTxt, 254, "%d", FqOffsetPPM );
			SendMessage(GetDlgItem(hwndDlg, IDC_PPM_S), UDM_SETRANGE, (WPARAM)0, (LPARAM)(1000 & 0xFFFF) | (((LPARAM)(-1000) << 16) & 0xFFFF0000) );
			Edit_SetText(GetDlgItem(hwndDlg, IDC_PPM), FreqoffsetTxt);

			//LNA Gain Reduction Threshold
			sprintf_s(LNAGRTHRESTtxt, 254, "%d", LNAGRTHRES);
			SendMessage(GetDlgItem(hwndDlg, IDC_LNASLIDER), TBM_SETRANGEMIN, (WPARAM)TRUE, (LPARAM)24);
			SendMessage(GetDlgItem(hwndDlg, IDC_LNASLIDER), TBM_SETRANGEMAX, (WPARAM)TRUE, (LPARAM)59);
			SendMessage(GetDlgItem(hwndDlg, IDC_LNASLIDER), TBM_SETPOS, (WPARAM)TRUE, (LPARAM)LNAGRTHRES);
			Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGRTHRES), LNAGRTHRESTtxt);

			//AGC Enabled
			SendMessage(GetDlgItem(hwndDlg, IDC_RSPAGC), BM_SETCHECK, (WPARAM)(AGCEnabled ? BST_CHECKED : BST_UNCHECKED), (LPARAM)0);
			SendMessage(GetDlgItem(hwndDlg, IDC_GR), WM_ENABLE, (WPARAM)(AGCEnabled ? 0 : 1), 1);
			if (AGCEnabled)
				m_timer = SetTimer(hwndDlg, ID_AGCUPDATE, 600, NULL);

			FreqBand = 0;
			while (Frequency > band_fmin[FreqBand + 1] && FreqBand + 1 < NUM_BANDS)
				FreqBand++;

			//LNA On
			if (GainReduction <= LNAGRTHRES)
			{
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGR), "LNA GR 0 dB");
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LNASTATE), "LNA ON");
				sprintf_s(str, sizeof(str), "IF Gain Reduction %d dB", GainReduction);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_IFGR), str);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_MIXERGR), "Mixer GR 0 dB");
				Edit_SetText(GetDlgItem(hwndDlg, IDC_MXRSTATE), "MIXER ON");
			}

			//LNA OFF
			if (GainReduction > LNAGRTHRES)
			{
				sprintf_s(str, sizeof(str), "LNA GR %d dB", band_LNAgain[FreqBand]);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGR), str);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LNASTATE), "LNA OFF");
				sprintf_s(str, sizeof(str), "IF Gain Reduction %d dB", GainReduction - band_LNAgain[FreqBand]);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_IFGR), str);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_MIXERGR), "Mixer GR 0 dB");
				Edit_SetText(GetDlgItem(hwndDlg, IDC_MXRSTATE), "MIXER ON");
			}

			//Mixer OFF
			if (GainReduction > (band_MaxGR[FreqBand] - band_MIXgain[FreqBand]))
			{
				sprintf_s(str, sizeof(str), "LNA GR %d dB", band_LNAgain[FreqBand]);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGR), str);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LNASTATE), "LNA OFF");
				sprintf_s(str, sizeof(str), "Mixer GR %d dB", band_MIXgain[FreqBand]);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_MIXERGR), str);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_MXRSTATE), "MIXER OFF");
				sprintf_s(str, sizeof(str), "IF Gain Reduction %d dB", GainReduction - band_LNAgain[FreqBand] - band_MIXgain[FreqBand]);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_IFGR), str);
			}
			return TRUE;
			break;

		case WM_COMMAND:
			switch (GET_WM_COMMAND_ID(wParam, lParam))
			{
			case IDC_Advanced:
				if (GET_WM_COMMAND_CMD(wParam, lParam) == BN_CLICKED)
				{
					if(h_AdvancedDialog == NULL)
						h_AdvancedDialog = CreateDialog(hInst, MAKEINTRESOURCE(IDD_ADVANCED), NULL, (DLGPROC)AdvancedDlgProc);  //(DLGPROC)AdvancedDlgProc
					ShowWindow(h_AdvancedDialog, SW_SHOW); 
					SetForegroundWindow(h_AdvancedDialog);
					return TRUE;
				}

			case IDC_SAMPLERATE:
				if (GET_WM_COMMAND_CMD(wParam, lParam) == CBN_SELCHANGE)
				{
					TCHAR SampleRateTxt[255];
					double WantedSR;

					//Get SampleRateDisplayIdx and Wanted SampleRate
					SampleRateDisplayIdx = ComboBox_GetCurSel(GET_WM_COMMAND_HWND(wParam, lParam));
					SendMessage(GetDlgItem(hwndDlg, IDC_SAMPLERATE), CB_GETLBTEXT, SampleRateDisplayIdx, (LPARAM)SampleRateTxt);
					WantedSR = atof(SampleRateTxt);

					SampleRateIdx = FindSampleRateIdx(WantedSR);

					WinradCallBack(-1, WINRAD_SRCHANGE, 0, NULL);

					return TRUE;
				}
		
			case IDC_BUFFER:
				if (GET_WM_COMMAND_CMD(wParam, lParam) == CBN_SELCHANGE)
				{
					buffer_default = ComboBox_GetCurSel(GET_WM_COMMAND_HWND(wParam, lParam));
					if (Running)
					{
						//StopHW();
						buffer_len_samples = buffer_sizes[buffer_default] * 1024;
						WinradCallBack(-1, WINRAD_SRCHANGE, 0, NULL);
						::Sleep(200);
					}
					else
						buffer_len_samples = buffer_sizes[buffer_default] * 1024;
					return TRUE;
				}
			case IDC_LNAGRTHRES:
				if (GET_WM_COMMAND_CMD(wParam, lParam) == EN_UPDATE)
				{
					TCHAR GRThres[255];
					Edit_GetText((HWND)lParam, GRThres, 255);
					if (ghwndDlg)	// update only when already initialized!
						LNAGRTHRES = _ttoi(GRThres);
					if (Running == TRUE)
						SDRplayInitalise();
					return TRUE;
				}
	
			case IDC_RSPAGC:
				if (ghwndDlg)	// update only when already initialized!
				{
					if (GET_WM_COMMAND_CMD(wParam, lParam) == BST_UNCHECKED)
					{
						if (Button_GetCheck(GET_WM_COMMAND_HWND(wParam, lParam)) == BST_CHECKED) //it is checked
						{
							AGCEnabled = true;
							Edit_Enable(GetDlgItem(hwndDlg, IDC_GR), 0);
							Edit_Enable(GetDlgItem(hwndDlg, IDC_GAINSLIDER), 0);
							m_timer = SetTimer(hwndDlg, ID_AGCUPDATE, 600, NULL);
						}
						else
						{
							AGCEnabled = false;
							Edit_Enable(GetDlgItem(hwndDlg, IDC_GR), 1);
							Edit_Enable(GetDlgItem(hwndDlg, IDC_GAINSLIDER), 1);
							KillTimer(hwndDlg, ID_AGCUPDATE);
						}
					}			
				}
				return TRUE;

			case IDC_SETPOINT:
				if (GET_WM_COMMAND_CMD(wParam, lParam) == EN_UPDATE)
				{
					TCHAR SP[255];
					// need to have error checking applied here.
					Edit_GetText((HWND)lParam, SP, 255);
					if (ghwndDlg)	// update only when already initialized!
						AGCsetpoint = _ttoi(SP);
					if (Running == TRUE)
						SDRplayInitalise();
					return TRUE;
				}
			case IDC_PPM:
				if (GET_WM_COMMAND_CMD(wParam, lParam) == EN_UPDATE)
				{
					TCHAR Freqoffset[255];

					// need to have error checking applied here.
					Edit_GetText((HWND)lParam, Freqoffset, 255);

					if (ghwndDlg)	// update only when already initialized!
						FqOffsetPPM = atoi(Freqoffset);
					if (Running == TRUE)
						SDRplayInitalise();
					return TRUE;
				}
				return TRUE;
			
			case IDC_GR:
				if (GET_WM_COMMAND_CMD(wParam, lParam) == EN_UPDATE)
				{
					TCHAR GR[255];
					if (!AGCEnabled)
					{
						Edit_GetText((HWND)lParam, GR, 255);
						if (ghwndDlg)	// update only when already initialized!
							GainReduction = _ttoi(GR);
						SendMessage(GetDlgItem(hwndDlg, IDC_GAINSLIDER), TBM_SETPOS, (WPARAM)TRUE, (LPARAM)GainReduction);

						FreqBand = 0;
						while (Frequency > band_fmin[FreqBand + 1] && FreqBand + 1 < NUM_BANDS)
							FreqBand++;

						//LNA On
						if (GainReduction < LNAGRTHRES)
						{
							Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGR), "LNA GR 0 dB");
							Edit_SetText(GetDlgItem(hwndDlg, IDC_LNASTATE), "LNA ON");
							sprintf_s(str, sizeof(str), "IF Gain Reduction %d dB", GainReduction);
							Edit_SetText(GetDlgItem(hwndDlg, IDC_IFGR), str);
							Edit_SetText(GetDlgItem(hwndDlg, IDC_MIXERGR), "Mixer GR 0 dB");
							Edit_SetText(GetDlgItem(hwndDlg, IDC_MXRSTATE), "MIXER ON");
						}

						//LNA OFF
						if (GainReduction >= LNAGRTHRES)
						{
							sprintf_s(str, sizeof(str), "LNA GR %d dB", band_LNAgain[FreqBand]);
							Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGR), str);
							Edit_SetText(GetDlgItem(hwndDlg, IDC_LNASTATE), "LNA OFF");
							sprintf_s(str, sizeof(str), "IF Gain Reduction %d dB", GainReduction - band_LNAgain[FreqBand]);
							Edit_SetText(GetDlgItem(hwndDlg, IDC_IFGR), str);
							Edit_SetText(GetDlgItem(hwndDlg, IDC_MIXERGR), "Mixer GR 0 dB");
							Edit_SetText(GetDlgItem(hwndDlg, IDC_MXRSTATE), "MIXER ON");
						}

						//Mixer OFF
						if (GainReduction > (band_MaxGR[FreqBand] - band_MIXgain[FreqBand]))
						{
							sprintf_s(str, sizeof(str), "LNA GR %d dB", band_LNAgain[FreqBand]);
							Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGR), str);
							Edit_SetText(GetDlgItem(hwndDlg, IDC_LNASTATE), "LNA OFF");
							sprintf_s(str, sizeof(str), "Mixer GR %d dB", band_MIXgain[FreqBand]);
							Edit_SetText(GetDlgItem(hwndDlg, IDC_MIXERGR), str);
							Edit_SetText(GetDlgItem(hwndDlg, IDC_MXRSTATE), "MIXER OFF");
							sprintf_s(str, sizeof(str), "IF Gain Reduction %d dB", GainReduction - band_LNAgain[FreqBand] - band_MIXgain[FreqBand]);
							Edit_SetText(GetDlgItem(hwndDlg, IDC_IFGR), str);
						}

						if (Running == TRUE)
						{
							int programmed = 0;
							int count = 0;
							while (programmed == 0)
							{
								if (ThreadVariables.GrToggle != LastGrToggle)
								{
									SDRplayInitalise();
									programmed = 1;
								}
								else
								{
									programmed = 0;
									Sleep(25);
									if (count == 4)
									{
										SDRplayInitalise();
										programmed = 1;
									}
									count++;
								}
							}
						}
						return TRUE;
					}
					if (AGCEnabled)
					{
						return TRUE;
					}
				}
				return TRUE;

			case IDC_EXIT:
				if (GET_WM_COMMAND_CMD(wParam, lParam) == BN_CLICKED)
				{
					ShowWindow(h_dialog, SW_HIDE);
					if(h_AdvancedDialog != NULL)
						ShowWindow(h_AdvancedDialog, SW_HIDE);
				}
				return TRUE;

			case IDC_LoadDefaults:
				if (GET_WM_COMMAND_CMD(wParam, lParam) == BN_CLICKED)
				{
					//IF Mode
					IFMode = mir_sdr_IF_Zero;
					IFmodeIdx = 0;
					ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_IFMODE), IFmodeIdx);

					//Bandwidth
					ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_IFBW));
					_stprintf_s(str, 255, "200 kHz");
					ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
					_stprintf_s(str, 255, "300 kHz");
					ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
					_stprintf_s(str, 255, "600 kHz");
					ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
					_stprintf_s(str, 255, "1.536 MHz");
					ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
					_stprintf_s(str, 255, "5.000 MHz");
					ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
					_stprintf_s(str, 255, "6.000 MHz");
					ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
					_stprintf_s(str, 255, "7.000 MHz");
					ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
					_stprintf_s(str, 255, "8.000 MHz");
					ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
					BandwidthIdx = 3;
					BandwidthIdx = ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_IFBW), BandwidthIdx);
					Bandwidth = bandwidths[BandwidthIdx].bwType;

					//Samplerate
					SampleRateIdx = 8;
					ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_SAMPLERATE));
					for (int i = 0; i < (sizeof(SampleRate) / sizeof(SampleRate[0]))-1; i++)
					{
						SR = SampleRate[i].DisplayValue;
						_stprintf_s(str, 255, TEXT("%.2f"), SR);
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_SAMPLERATE), str);
					}
					ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_SAMPLERATE), SampleRateIdx);

					//Gain Reduction
					GainReduction = 50;
					sprintf_s(GainReductionTxt, 254, "%d", GainReduction);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_GR), GainReductionTxt);
					SendMessage(GetDlgItem(hwndDlg, IDC_GAINSLIDER), TBM_SETPOS, (WPARAM)TRUE, (LPARAM)GainReduction);

					//AGCSetpoint
					AGCsetpoint = -15;
					sprintf_s(AGCsetpointTxt, 254, "%d", AGCsetpoint);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_SETPOINT), AGCsetpointTxt);

					//Frequency Offset
					FqOffsetPPM = 0;
					sprintf_s(FreqoffsetTxt, 254, "%d", FqOffsetPPM);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_PPM), FreqoffsetTxt);

					//LNA Gain Threshold
					LNAGRTHRES = 59;
					sprintf_s(LNAGRTHRESTtxt, 254, "%d", LNAGRTHRES);
					Edit_SetText(GetDlgItem(hwndDlg, IDC_LNAGRTHRES), LNAGRTHRESTtxt);
					SendMessage(GetDlgItem(hwndDlg, IDC_LNASLIDER), TBM_SETPOS, (WPARAM)TRUE, (LPARAM)LNAGRTHRES);

					//AGC
					SendMessage(GetDlgItem(hwndDlg, IDC_GR), WM_ENABLE, (WPARAM)(AGCEnabled ? 0 : 1), 0);

					//LOPLan
					LOplan = LO120MHz;
					LOplanAuto = true;
					WinradCallBack(-1, WINRAD_SRCHANGE, 0, NULL);
					if (Running == TRUE)
					{
						SDRplayInitalise();
					}
				}
				DcCompensationMode = PERIODIC3;
				TrackingPeriod = 32;
				RefreshPeriodMemory = 2;
				return true;
			
			case IDC_IFBW:
				if (GET_WM_COMMAND_CMD(wParam, lParam) == CBN_SELCHANGE)
				{
					double SR, WantedSR;
					float BW;
					TCHAR str[255];
										
					BandwidthIdx = ComboBox_GetCurSel(GET_WM_COMMAND_HWND(wParam, lParam));
					Bandwidth = bandwidths[BandwidthIdx].bwType;
					BW = (float)bandwidths[BandwidthIdx].BW;

					//ZIF Mode selected
					if (IFmodeIdx == 0)
					{
						ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_SAMPLERATE));									//Populate Control With Appropriate Sample rates
						for (int i = 0; i < (sizeof(SampleRate) / sizeof(SampleRate[0])) - 1; i++)
						{
							SR = SampleRate[i].DisplayValue + 0.01;														//Subtract small value as cannot use == with two doubles.
							if (SR > BW)
							{
								_stprintf_s(str, 255, TEXT("%.2f"), SampleRate[i].DisplayValue);
								ComboBox_AddString(GetDlgItem(hwndDlg, IDC_SAMPLERATE), str);
							}
						}
						SampleRateDisplayIdx = 0;
						ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_SAMPLERATE), SampleRateDisplayIdx);
						SendMessage(GetDlgItem(hwndDlg, IDC_SAMPLERATE), CB_GETLBTEXT, 0, (LPARAM)SampleRateTxt);	//readback chosen sample rates and work out Idx
						WantedSR = atof(SampleRateTxt);

						SampleRateIdx = FindSampleRateIdx(WantedSR);
					}
					//LIF Mode selected
					if (IFmodeIdx == 1)
					{
						if (Bandwidth == mir_sdr_BW_1_536)
						{
							IFMode = mir_sdr_IF_2_048;
							SampleRateIdx = 15;
							SampleRateDisplayIdx = 0;
							ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_SAMPLERATE));
							_stprintf_s(str, 255, TEXT("%.2f"), SampleRate[SampleRateIdx].DisplayValue);
							ComboBox_AddString(GetDlgItem(hwndDlg, IDC_SAMPLERATE), str);
							ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_SAMPLERATE), SampleRateDisplayIdx);
						}
						if (Bandwidth == mir_sdr_BW_0_200 || Bandwidth == mir_sdr_BW_0_300 || Bandwidth == mir_sdr_BW_0_600)
						{
							IFMode = mir_sdr_IF_0_450;
							SampleRateIdx = 8;
							SampleRateDisplayIdx = 0;
							ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_SAMPLERATE));
							_stprintf_s(str, 255, TEXT("%.2f"), SampleRate[SampleRateIdx].DisplayValue);
							ComboBox_AddString(GetDlgItem(hwndDlg, IDC_SAMPLERATE), str);
							ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_SAMPLERATE), SampleRateDisplayIdx);
						}
					}

					WinradCallBack(-1, WINRAD_SRCHANGE, 0, NULL);
					if (Running == TRUE)
					{
						SDRplayInitalise();
					}
					return TRUE;
				}

			case IDC_IFMODE:
				if (GET_WM_COMMAND_CMD(wParam, lParam) == CBN_SELCHANGE)
				{
					int i;
					double SR;
					TCHAR str[255];

					IFmodeIdx = ComboBox_GetCurSel(GET_WM_COMMAND_HWND(wParam, lParam));
					if (IFmodeIdx == 0)
					{
						//Add Filter Bandwidths to IFBW dialog Box
						ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_IFBW));
						_stprintf_s(str, 255, "200 kHz");
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
						_stprintf_s(str, 255, "300 kHz");
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
						_stprintf_s(str, 255, "600 kHz");
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
						_stprintf_s(str, 255, "1.536 MHz");
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
						_stprintf_s(str, 255, "5.000 MHz");
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
						_stprintf_s(str, 255, "6.000 MHz");
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
						_stprintf_s(str, 255, "7.000 MHz");
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
						_stprintf_s(str, 255, "8.000 MHz");
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);	

						//Set IF Bandwidth to 200kHz as Default
						BandwidthIdx = 0;
						ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_IFBW), BandwidthIdx);
						Bandwidth = bandwidths[BandwidthIdx].bwType;

						//Set IF Mode to ZIF
						IFMode = mir_sdr_IF_Zero;

						//Set Samplerate for 200kHz filter default
						SampleRateIdx = 0;
						SampleRateDisplayIdx = 0;
						ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_SAMPLERATE));
						for (i = 0; i < (sizeof(SampleRate) / sizeof(SampleRate[0])) - 1; i++)
						{
							SR = SampleRate[i].DisplayValue;
							_stprintf_s(str, 255, TEXT("%.2f"), SR);
							ComboBox_AddString(GetDlgItem(hwndDlg, IDC_SAMPLERATE), str);
						}
						ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_SAMPLERATE), SampleRateDisplayIdx);

						//Disable Sample Rate Dialog Box
						Edit_Enable(GetDlgItem(hwndDlg, IDC_SAMPLERATE), 1);
					}

					if (IFmodeIdx == 1)
					{
						//Add filter Bandwidths for Low IF modes
						ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_IFBW));
						_stprintf_s(str, 255, "200 kHz");
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
						_stprintf_s(str, 255, "300 kHz");
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
						_stprintf_s(str, 255, "600 kHz");
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);
						_stprintf_s(str, 255, "1.536 MHz");						
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_IFBW), str);	

						//Set IF Bandwidth to 200kHz as Default
						BandwidthIdx = 0;
						ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_IFBW), BandwidthIdx);
						Bandwidth = bandwidths[BandwidthIdx].bwType;

						//IF Mode
						IFMode = mir_sdr_IF_0_450;

						//Set Samplerate for 200kHz filter default
						SampleRateIdx = 8;
						SampleRateDisplayIdx = 0;
						ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_SAMPLERATE));
						_stprintf_s(str, 255, TEXT("%.2f"), SampleRate[SampleRateIdx].DisplayValue);
						ComboBox_AddString(GetDlgItem(hwndDlg, IDC_SAMPLERATE), str);
						ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_SAMPLERATE), SampleRateDisplayIdx);

						//Disable Sample Rate Display.
						Edit_Enable(GetDlgItem(hwndDlg, IDC_SAMPLERATE), 0);
					}

					if (Running == TRUE)
					{
						WinradCallBack(-1, WINRAD_SRCHANGE, 0, NULL);
					}
					return TRUE;
				}
			}
		}
		return FALSE;
	}

static INT_PTR CALLBACK AdvancedDlgProc(HWND hwndDlg, UINT uMsg, WPARAM wParam, LPARAM lParam)
{
	static HWND hGain;
	static HBRUSH BRUSH_RED = CreateSolidBrush(RGB(255, 0, 0));
	static HBRUSH BRUSH_GREEN = CreateSolidBrush(RGB(0, 255, 0));
	int periodic;
	TCHAR str[255];
	int FreqBand = 0;
	static bool LOplanAutoLCL;
	static int LOplanLCL;
	static int DcCompensationModeLCL;
	static int RefreshPeriodMemoryLCL;
	static bool PostTunerDcCompensationLCL;

	switch (uMsg)
	{
	case WM_CLOSE:
		ShowWindow(h_AdvancedDialog, SW_HIDE);
		return TRUE;
		break;

	case WM_HSCROLL:
		if ((HWND)lParam == GetDlgItem(hwndDlg, IDC_TRACKINGPERIOD))
		{
			TrackingPeriod = SendMessage(GetDlgItem(hwndDlg, IDC_TRACKINGPERIOD), TBM_GETPOS, (WPARAM)0, (LPARAM)0);
			TrackTime = TrackingPeriod *DCTrackTimeInterval;
			sprintf_s(str, 254, "%.2f uS", TrackTime);
			Edit_SetText(GetDlgItem(hwndDlg, IDC_TRACKTIME), str);
		}
		return TRUE;
		break;

	case WM_DESTROY:
		h_AdvancedDialog = NULL;
		return TRUE;
		break;

	case WM_INITDIALOG:
		// LO Planning
		if (LOplanAuto == true)
		{
			SendMessage(GetDlgItem(hwndDlg, IDC_LOAUTO), BM_SETCHECK, BST_CHECKED, 0);
			Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING), "Full Coverage");
			Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING1), " ");
		}
		else
		{
			if (LOplan == LO120MHz)
			{
				SendMessage(GetDlgItem(hwndDlg, IDC_LO120), BM_SETCHECK, BST_CHECKED, 0);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING), "Coverage gap between 370MHz and 420MHz");
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING1), " ");
			}
			if (LOplan == LO144MHz)
			{
				SendMessage(GetDlgItem(hwndDlg, IDC_LO144), BM_SETCHECK, BST_CHECKED, 0);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING), "Coverage gaps between 250MHz to 255MHz");
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING1), "Coverage gaps between 400MHz to 420MHz");
			}
			if (LOplan == LO168MHz)
			{
				SendMessage(GetDlgItem(hwndDlg, IDC_LO168), BM_SETCHECK, BST_CHECKED, 0);
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING), "Coverage gap between 250MHz and 265MHz");
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING1), " ");
			}
		}

		//Tracking period
		SendMessage(GetDlgItem(hwndDlg, IDC_TRACKINGPERIOD), TBM_SETRANGEMIN, (WPARAM)TRUE, (LPARAM)1);
		SendMessage(GetDlgItem(hwndDlg, IDC_TRACKINGPERIOD), TBM_SETRANGEMAX, (WPARAM)TRUE, (LPARAM)63);
		SendMessage(GetDlgItem(hwndDlg, IDC_TRACKINGPERIOD), TBM_SETPOS, (WPARAM)TRUE, (LPARAM)TrackingPeriod);
		TrackTime = TrackingPeriod *DCTrackTimeInterval;
		sprintf_s(str, 254, "%.2f uS", TrackTime);
		Edit_SetText(GetDlgItem(hwndDlg, IDC_TRACKTIME), str);

		//Populate the refresh period
		ComboBox_ResetContent(GetDlgItem(hwndDlg, IDC_REFRESH));
		ComboBox_AddString(GetDlgItem(hwndDlg, IDC_REFRESH), "6mS");
		ComboBox_AddString(GetDlgItem(hwndDlg, IDC_REFRESH), "12mS");
		ComboBox_AddString(GetDlgItem(hwndDlg, IDC_REFRESH), "24mS");
		ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_REFRESH), RefreshPeriodMemory);

		//DC Offset Compensation
		if (DcCompensationMode == STATIC)
		{
			SendMessage(GetDlgItem(hwndDlg, IDC_DCSTAT), BM_SETCHECK, BST_CHECKED, 0);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_REFRESH), 0);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKINGPERIOD), 0);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKTIME), 0);
		}
		if (DcCompensationMode == ONESHOT)
		{
			SendMessage(GetDlgItem(hwndDlg, IDC_ONESHOT), BM_SETCHECK, BST_CHECKED, 0);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_REFRESH), 0);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKINGPERIOD), 1);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKTIME), 1);
		}
		if (DcCompensationMode == CONTINUOUS)
		{
			SendMessage(GetDlgItem(hwndDlg, IDC_CONTINUOUS), BM_SETCHECK, BST_CHECKED, 0);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_REFRESH), 0);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKINGPERIOD), 0);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKTIME), 0);
		}
		if (DcCompensationMode == PERIODIC1 || DcCompensationMode == PERIODIC2 || DcCompensationMode == PERIODIC3)
		{
			SendMessage(GetDlgItem(hwndDlg, IDC_PERIODIC), BM_SETCHECK, BST_CHECKED, 0);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_REFRESH), 1);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKINGPERIOD), 1);
			Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKTIME), 1);
			if (DcCompensationMode == PERIODIC1)
			{
				ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_REFRESH), 0);
			}
			if (DcCompensationMode == PERIODIC2)
			{
				ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_REFRESH), 1);
			}
			if (DcCompensationMode == PERIODIC3)
			{
				ComboBox_SetCurSel(GetDlgItem(hwndDlg, IDC_REFRESH), 2);
			}
		}

		//Post Tuner DC Compensdation
		if (PostTunerDcCompensation == TRUE)
			SendMessage(GetDlgItem(hwndDlg, IDC_POSTDCOFFSET), BM_SETCHECK, BST_CHECKED, 0);
		else
			SendMessage(GetDlgItem(hwndDlg, IDC_POSTDCOFFSET), BM_SETCHECK, BST_UNCHECKED, 0);

		LOplanAutoLCL = LOplanAuto;
		LOplanLCL = LOplan;
		DcCompensationModeLCL = DcCompensationMode;
		RefreshPeriodMemoryLCL = RefreshPeriodMemory;
		PostTunerDcCompensationLCL = PostTunerDcCompensation;
		return TRUE;
		break;

	case WM_COMMAND:
		switch (GET_WM_COMMAND_ID(wParam, lParam))
		{
		case IDC_ADVANCED_EXIT:
			ShowWindow(h_AdvancedDialog, SW_HIDE);
			h_AdvancedDialog = NULL;
			return TRUE;
			break;

		case IDC_ADVANCED_APPLY:
			LOplanAuto =LOplanAutoLCL;
			LOplan = LOplanLCL;
			DcCompensationMode = DcCompensationModeLCL;
			RefreshPeriodMemory = RefreshPeriodMemoryLCL;
			PostTunerDcCompensation = PostTunerDcCompensationLCL;
			SDRplayInitalise();
			return TRUE;
			break;

		case IDC_LOAUTO:
			if (GET_WM_COMMAND_CMD(wParam, lParam) == BN_CLICKED)
			{
				LOplanAutoLCL = true;
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING), "Full Coverage");
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING1), " ");
			}
			return TRUE;
			break;

		case IDC_LO120:
			if (GET_WM_COMMAND_CMD(wParam, lParam) == BN_CLICKED)
			{
				LOplanAutoLCL = false;
				LOplanLCL = LO120MHz;
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING), "Coverage gap between 370MHz and 420MHz");
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING1), " ");
				MessageBox(NULL, "By selecting this LO PLan there will be a coverage gap between 370MHz and 420MHz", TEXT("SDRplay ExtIO DLL Warning"), MB_OK | MB_SYSTEMMODAL | MB_TOPMOST | MB_ICONEXCLAMATION);
			}
			return TRUE;
			break;

		case IDC_LO144:
			if (GET_WM_COMMAND_CMD(wParam, lParam) == BN_CLICKED)
			{
				LOplanAutoLCL = false;
				LOplanLCL = LO144MHz;
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING), "Coverage gaps between 250MHz to 255MHz");
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING1), "Coverage gaps between 400MHz to 420MHz");
				MessageBox(NULL, "By selecting this LO PLan there will be coverage gaps between 250MHz to 255MHz and 400MHz to 420MHz", TEXT("SDRplay ExtIO DLL Warning"), MB_OK | MB_SYSTEMMODAL | MB_TOPMOST | MB_ICONEXCLAMATION);
			}
			return TRUE;
			break;

		case IDC_LO168:
			if (GET_WM_COMMAND_CMD(wParam, lParam) == BN_CLICKED)
			{
				LOplanAutoLCL = false;
				LOplanLCL = LO168MHz;
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING), "Coverage gap between 250MHz and 265MHz");
				Edit_SetText(GetDlgItem(hwndDlg, IDC_LOWARNING1), " ");
				MessageBox(NULL, "By selecting this LO PLan there will be a coverage gap between 250MHz and 265MHz", TEXT("SDRplay ExtIO DLL Warning"), MB_OK | MB_SYSTEMMODAL | MB_TOPMOST | MB_ICONEXCLAMATION);
			}
			return TRUE;
			break;

		case IDC_POSTDCOFFSET:
			if (GET_WM_COMMAND_CMD(wParam, lParam) == BN_CLICKED)
			{
				if (Button_GetCheck(GET_WM_COMMAND_HWND(wParam, lParam)) == BST_CHECKED)
					PostTunerDcCompensationLCL = TRUE;
				else
					PostTunerDcCompensationLCL = FALSE;
			}
			return TRUE;
			break;

		case IDC_DCSTAT:
			if (GET_WM_COMMAND_CMD(wParam, lParam) == BN_CLICKED)
			{
				DcCompensationModeLCL = STATIC;
				Edit_Enable(GetDlgItem(hwndDlg, IDC_REFRESH), 0);
				Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKINGPERIOD), 0);
				Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKTIME), 0);
			}
			return TRUE;
			break;

		case IDC_ONESHOT:
			if (GET_WM_COMMAND_CMD(wParam, lParam) == BN_CLICKED)
			{
				DcCompensationModeLCL = ONESHOT;
				Edit_Enable(GetDlgItem(hwndDlg, IDC_REFRESH), 0);
				Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKINGPERIOD), 1);
				Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKTIME), 1);
			}
			return TRUE;
			break;

		case IDC_CONTINUOUS:
			if (GET_WM_COMMAND_CMD(wParam, lParam) == BN_CLICKED)
			{
				DcCompensationModeLCL = CONTINUOUS;
				Edit_Enable(GetDlgItem(hwndDlg, IDC_REFRESH), 0);
				Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKINGPERIOD), 0);
				Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKTIME), 0);
			}
			return TRUE;
			break;

		case IDC_PERIODIC:
			if (GET_WM_COMMAND_CMD(wParam, lParam) == BN_CLICKED)
			{
				Edit_Enable(GetDlgItem(hwndDlg, IDC_REFRESH), 1);
				Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKINGPERIOD), 1);
				Edit_Enable(GetDlgItem(hwndDlg, IDC_TRACKTIME), 1);
				periodic = ComboBox_GetCurSel(GetDlgItem(hwndDlg, IDC_REFRESH));
				if (periodic == 0)
				{
					DcCompensationModeLCL = PERIODIC1;
					RefreshPeriodMemoryLCL = 0;
				}
				if (periodic == 1)
				{
					DcCompensationModeLCL = PERIODIC2;
					RefreshPeriodMemoryLCL = 1;
				}
				if (periodic == 2)
				{
					DcCompensationModeLCL = PERIODIC3;
					RefreshPeriodMemoryLCL = 2;
				}
			}
			return TRUE;
			break;

		case IDC_REFRESH:
			if (GET_WM_COMMAND_CMD(wParam, lParam) == CBN_SELCHANGE)
			{
				periodic = ComboBox_GetCurSel(GET_WM_COMMAND_HWND(wParam, lParam));
				if (periodic == 0)
				{
					DcCompensationModeLCL = PERIODIC1;
					RefreshPeriodMemoryLCL = 0;
				}
				if (periodic == 1)
				{
					DcCompensationModeLCL = PERIODIC2;
					RefreshPeriodMemoryLCL = 1;
				}
				if (periodic == 2)
				{
					DcCompensationModeLCL = PERIODIC3;
					RefreshPeriodMemoryLCL = 2;
				}
			}
			return TRUE;
			break;
		}
	}
	return FALSE;
}
*/
